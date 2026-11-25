import OAI.Computability.BorderVNP.TeamSitePrivate
import OAI.Computability.BorderVNP.TeamBurstProbeReplay

/-! # Exact choice streams for the signed processor's instruction events

The physical processor guesses a previous word from high bit to low bit. It consumes
all consecutive old words before taking an instruction or private routine's own
choices. The decoder below realizes this order, including for zero-length bursts
and zero-weight private halts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSiteEvents

open VPVNP RAMTape BurstRAM TeamSiteChoices TeamPrivateTape

variable {Q Γ : Type} {w p r a m g d : ℕ}

/-- Whether a finite list is the initial segment consumed from the given supply. -/
def Prefix (s : Supply) (bs : List Bool) : Prop := takeBits s bs.length = bs

theorem prefix_nil (s : Supply) : Prefix s [] := rfl

@[simp] theorem prefix_cons_iff (s : Supply) (b : Bool) (bs : List Bool) :
    Prefix s (b::bs) ↔ s 0 = b ∧ Prefix (drop s 1) bs := by
  simp only [Prefix, List.length_cons, prefix_succ, List.cons.injEq]

/-- Split the branch supply at the end of an encoded segment. -/
theorem prefix_append (s : Supply) (x y : List Bool) :
    Prefix s (x ++ y) ↔ Prefix s x ∧ Prefix (drop s x.length) y := by
  simp only [Prefix, List.length_append, prefix_add]
  exact ⟨fun h => List.append_inj h (prefix_length s _), fun ⟨hx,hy⟩ => congrArg₂ List.append hx hy⟩

/-- Decode one fixed-width word in the actual order of the nondeterministic rows. -/
def readWord (w : ℕ) (s : Supply) : Word w :=
  ⟨TapeWord.value (takeBits s w).reverse, by
    simpa only [List.length_reverse, prefix_length] using TapeWord.value_lt (takeBits s w).reverse⟩

@[simp] theorem readWord_bits (s : Supply) :
    (wordBits (readWord w s)).reverse = takeBits s w := by
  have eq : wordBits (readWord w s) = (takeBits s w).reverse := TapeWord.eq_of_length_value
    (by simp) (TapeWord.value_wordBits _)
  simp [eq]

/-- Decode a consecutive sequence of probe guesses, including the empty sequence. -/
def readWords (w : ℕ) : ℕ → Supply → List (Word w)
  | 0, _ => []
  | q+1, s => readWord w s :: readWords w q (drop s w)

@[simp] theorem readWords_length (s : Supply) (q : ℕ) : (readWords w q s).length = q := by
  induction q generalizing s <;> simp [readWords, *]

/-- Each word occupies exactly its advertised width on the physical branch stream. -/
theorem choices_length (vs : List (Word w)) : (TeamBurstProbe.choices vs).length = vs.length*w := by
  induction vs with
  | nil => simp [TeamBurstProbe.choices]
  | cons v vs ih =>
    change ((wordBits v).reverse ++ TeamBurstProbe.choices vs).length = (vs.length+1)*w
    simp only [List.length_append, List.length_reverse, length_wordBits, ih, Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- Reading words consumes exactly the physical guess prefix. -/
theorem readWords_prefix (s : Supply) (q : ℕ) : Prefix s (TeamBurstProbe.choices (readWords w q s)) := by
  induction q generalizing s with
  | zero => rfl
  | succ q ih =>
    rw [readWords, TeamBurstProbe.choices, List.flatMap_cons, prefix_append]
    constructor
    · simp only [Prefix, readWord_bits, prefix_length]
    · change Prefix (drop s (wordBits (readWord w s)).reverse.length) (TeamBurstProbe.choices _)
      simpa only [List.length_reverse, length_wordBits] using ih (drop s w)

/-- A well-sized list of claimed words is uniquely determined by its encoded prefix. -/
theorem readWords_eq (s : Supply) (vs : List (Word w)) (h : Prefix s (TeamBurstProbe.choices vs)) :
    readWords w vs.length s = vs := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih =>
    obtain ⟨head, tail⟩ := (prefix_append s (wordBits v).reverse (TeamBurstProbe.choices vs)).mp h
    have bits : (wordBits (readWord w s)).reverse = (wordBits v).reverse := by
      simpa only [readWord_bits, Prefix, List.length_reverse, length_wordBits] using head
    have eq : readWord w s = v := by
      apply Fin.ext
      simpa only [List.reverse_reverse, TapeWord.value_wordBits] using
        congrArg TapeWord.value (congrArg List.reverse bits)
    rw [List.length_cons, readWords, eq, ih (drop s w) (by simpa only [List.length_reverse, length_wordBits] using tail)]

/-- Run a private table on a supply, collecting only the bits at actual choice rows. -/
def readPrivate (P : Table Q d) : ℕ → Q → (Fin d → Track) → Supply →
    Option (List Bool × Option Bool × (Fin d → Track))
  | 0, _, _, _ => none
  | fuel+1, q, t, s => match P q (heads t) with
    | .halt accept neg => some ([], if accept then some neg else none, t)
    | .one c => readPrivate P fuel c.next (c.apply t) s
    | .two l r =>
      let b := s 0
      let c := if b then r else l
      (readPrivate P fuel c.next (c.apply t) (drop s 1)).map (fun z => (b :: z.1, z.2))

/-- The supply evaluator follows exactly the finite native path, with no surplus
or missing choice allowed. This also covers rejecting private halts. -/
theorem readPrivate_iff (P : Table Q d) (fuel : ℕ) (q : Q) (t : Fin d → Track)
    (s : Supply) (bs : List Bool) (out : Option Bool) (u : Fin d → Track) :
    readPrivate P fuel q t s = some (bs,out,u) ↔
      TeamPrivateCall.evaluate P fuel q t bs = some (out,u) ∧ Prefix s bs := by
  induction fuel generalizing q t bs s with
  | zero => simp [readPrivate, TeamPrivateCall.evaluate]
  | succ fuel ih =>
    cases h : P q (heads t) with
    | halt acc neg =>
      cases bs <;> simp [readPrivate, TeamPrivateCall.evaluate, h, prefix_nil]
    | one c => simpa [readPrivate, TeamPrivateCall.evaluate, h] using ih c.next (c.apply t) s bs
    | two l r =>
      cases bs with
      | nil => simp [readPrivate, TeamPrivateCall.evaluate, h, Option.map_eq_some_iff]
      | cons b bs =>
        by_cases hb : s 0 = b
        · simp only [readPrivate, TeamPrivateCall.evaluate, h, hb, prefix_cons_iff, true_and]
          rw [Option.map_eq_some_iff]
          constructor
          · rintro ⟨⟨cs,z,v⟩, he, heq⟩
            obtain ⟨rfl,rfl,rfl⟩ : cs = bs ∧ z = out ∧ v = u := by simpa using heq
            exact (ih ..).mp he
          · intro he; exact ⟨(bs,out,u), (ih ..).mpr he, rfl⟩
        · simp [readPrivate, TeamPrivateCall.evaluate, h, hb, Option.map_eq_some_iff]

/-- The native signed macros appearing in the instruction model. -/
noncomputable def macros (lib : Fin a → TeamSite.Macro Q Γ m g) (fuel : ℕ) : TeamOpcode.Macros w a :=
  fun j => (lib j).eval fuel

/-- Instruction-level branch prefix after reading every guessed word. -/
noncomputable def branches (lib : Fin a → TeamSite.Macro Q Γ m g) (fuel : ℕ)
    (out : TeamOpcode.Exit p r a) (vs : List (Word w)) (s : Supply) : Option (List Bool) :=
  match out with
  | .native (.choose ..) => some [s 0]
  | .call j .. =>
    let M := lib j
    (readPrivate (trackTable M.alphabet M.table) fuel M.start (M.initial vs) s).map Prod.fst
  | _ => some []

/-- Number of old-word guesses required by a fetched action. -/
def probes : TeamTranscript.Action (Word w) → ℕ
  | .ordinary none => 0
  | .ordinary (some _) => 1
  | .burst _ q => q

/-- A generated event and its successor architectural state. -/
structure Next (w p r : ℕ) where
  /-- Full external action, claimed previous words, native choices and returned sign. -/
  event : TeamRAM.Event w
  /-- Architectural continuation selected by this instruction. -/
  state : TeamOpcode.State w p r

/-- Concatenate the processor's word-guess choices and the instruction's native choices. -/
def Next.bits (z : Next w p r) := TeamBurstProbe.choices z.event.old ++ z.event.choices

/-- Decode the actual signed RAM event on a branch supply. The cap and address range
are checked before any guess. Native halts and invalid instructions have no event. -/
noncomputable def generate (lib : Fin a → TeamSite.Macro Q Γ m g) (fuel cap : ℕ)
    (bank : PrivateRAM.LogConfig w p r) (out : TeamOpcode.Exit p r a) (s : Supply) : Option (Next w p r) := do
  let i := out.action (macros lib fuel) bank
  let act ← i.action
  guard (act.extra ≤ cap)
  let vs := readWords w (probes act) s
  let bs ← branches lib fuel out vs (drop s (probes act * w))
  let (next, sign) ← i.advance bs vs
  return ⟨⟨act, vs, bs, sign⟩, next⟩


/-- The external action fixes the number of old words of every enabled transition. -/
theorem old_length {S : Type*} {i : TeamRAM.Instr w S} {act bs vs t sg}
    (action : i.action = some act) (adv : i.advance bs vs = some (t, sg)) :
    vs.length = probes act := by
  cases i with
  | accept | reject => contradiction
  | localStep | choose | load | store =>
    obtain rfl := Option.some.inj action
    rcases vs with _ | ⟨v, _ | ⟨u,vs⟩⟩ <;> rcases bs with _ | ⟨b, _ | ⟨c,bs⟩⟩ <;>
      first | rfl | contradiction
  | call addr q run next =>
    by_cases h : addr.val+q ≤ 2^w
    · obtain rfl : TeamTranscript.Action.burst addr.val q = act := by simpa [TeamRAM.Instr.action,h] using action
      by_contra hq
      change vs.length ≠ q at hq
      simp [TeamRAM.Instr.advance, hq] at adv
    · simp [TeamRAM.Instr.action,h] at action

private theorem private_branches_iff (lib : Fin a → TeamSite.Macro Q Γ m g) (fuel : ℕ)
    (j : Fin a) (addr len : Fin r) (pc : Fin p) (vs : List (Word w)) (s : Supply) (bs : List Bool) :
    branches lib fuel (.call j addr len pc) vs s = some bs ↔
      (∃ sign, (lib j).eval fuel vs bs = some sign) ∧ Prefix s bs := by
  change ((readPrivate _ _ _ _ _).map Prod.fst = some _) ↔ _
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨cs,out,u⟩, hr, rfl⟩
    obtain ⟨he,hp⟩ := (readPrivate_iff ..).mp hr
    exact ⟨⟨TeamPrivateCall.sign out, by simp [TeamSite.Macro.eval,he]⟩,hp⟩
  · rintro ⟨⟨sign, he⟩, hp⟩
    obtain ⟨⟨out,u⟩,hr,_⟩ := Option.map_eq_some_iff.mp he
    exact ⟨(bs,out,u), (readPrivate_iff ..).mpr ⟨hr,hp⟩,rfl⟩

private theorem branches_prefix (lib : Fin a → TeamSite.Macro Q Γ m g) (fuel : ℕ)
    (out : TeamOpcode.Exit p r a) (vs : List (Word w)) (s : Supply) (bs : List Bool)
    (h : branches lib fuel out vs s = some bs) : Prefix s bs := by
  cases out with
  | sign => obtain rfl := Option.some.inj h; rfl
  | call j addr len pc => exact ((private_branches_iff ..).mp h).2
  | native cb =>
    cases cb <;> obtain rfl := Option.some.inj h <;> rfl

private theorem branches_of_advance (lib : Fin a → TeamSite.Macro Q Γ m g) (fuel : ℕ)
    (bank : PrivateRAM.LogConfig w p r) (out : TeamOpcode.Exit p r a) (vs : List (Word w))
    (s : Supply) (bs : List Bool) {t sg}
    (ha : (out.action (macros lib fuel) bank).advance bs vs = some (t,sg))
    (hp : Prefix s bs) : branches lib fuel out vs s = some bs := by
  cases out with
  | call j addr len pc =>
    apply (private_branches_iff ..).mpr
    change (if vs.length = _ then ((lib j).eval fuel vs bs).map _ else none) = some (t,sg) at ha
    split at ha
    · obtain ⟨z,he,_⟩ := Option.map_eq_some_iff.mp ha
      exact ⟨⟨z,he⟩,hp⟩
    · contradiction
  | sign =>
    cases bs <;> first | rfl | contradiction
  | native cb =>
    cases cb with
    | choose =>
      rcases bs with _ | ⟨b, _ | ⟨c,bs⟩⟩
      · contradiction
      · change some [s 0] = some [b]
        rw [(prefix_cons_iff ..).mp hp |>.1]
      · contradiction
    | next | read | write | accept | reject | returnState =>
      cases bs <;> first | rfl | contradiction

/-- A successful event follows the fetched transition and the exact physical choice
prefix. Conversely each event with those properties is the decoder's unique result. -/
theorem generate_iff (lib : Fin a → TeamSite.Macro Q Γ m g) (fuel cap : ℕ)
    (bank : PrivateRAM.LogConfig w p r) (out : TeamOpcode.Exit p r a) (s : Supply) (z : Next w p r) :
    generate lib fuel cap bank out s = some z ↔
      (out.action (macros lib fuel) bank).action = some z.event.action ∧
      (out.action (macros lib fuel) bank).advance z.event.choices z.event.old = some (z.state,z.event.sign) ∧
      z.event.action.extra ≤ cap ∧ Prefix s z.bits := by
  constructor
  · intro hg
    simp only [generate, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨act,ha,u,guardOk,bs,hb,⟨t,sg⟩,hn,hz⟩ := hg
    have hc : act.extra ≤ cap := by by_contra h; simp [h] at guardOk
    obtain rfl := Option.some.inj hz
    refine ⟨ha,hn,hc,(prefix_append ..).mpr ⟨readWords_prefix ..,?_⟩⟩
    simpa only [choices_length, readWords_length] using branches_prefix lib fuel out _ _ bs hb
  · rintro ⟨ha,hn,hc,hp⟩
    obtain ⟨hw,hb⟩ := (prefix_append ..).mp hp
    have hl := old_length ha hn
    have hv : readWords w (probes z.event.action) s = z.event.old := hl ▸ readWords_eq s z.event.old hw
    have hb' := branches_of_advance lib fuel bank out z.event.old
      (drop s (probes z.event.action * w)) z.event.choices hn (by simpa only [choices_length, hl] using hb)
    rcases z with ⟨⟨act,vs,bs,sg⟩,t⟩
    simp only at ha hn hc hv hb'
    simp [generate, ha, hc, hv, hb', hn]

/-- Any locally valid event within the burst cap can be replayed with its own finite
choice list as a prefix; the extension contributes no extra choices. -/
theorem generate_extend (lib : Fin a → TeamSite.Macro Q Γ m g) (fuel cap : ℕ)
    (bank : PrivateRAM.LogConfig w p r) (out : TeamOpcode.Exit p r a) (z : Next w p r)
    (act : (out.action (macros lib fuel) bank).action = some z.event.action)
    (adv : (out.action (macros lib fuel) bank).advance z.event.choices z.event.old = some (z.state,z.event.sign))
    (bounded : z.event.action.extra ≤ cap) :
    generate lib fuel cap bank out (extend z.bits) = some z :=
  (generate_iff ..).mpr ⟨act,adv,bounded,prefix_extend _⟩


/-- For an admissibly clocked private machine, a call produces an event on every
supply exactly when both its size and its address interval pass the physical checks. -/
theorem call_isSome_iff (lib : Fin a → TeamSite.Macro Q Γ m g) (fuel cap : ℕ)
    (bank : PrivateRAM.LogConfig w p r) (j : Fin a) (addr len : Fin r) (pc : Fin p) (s : Supply)
    (bound : (bank.reg len).val ≤ cap → (bank.reg addr).val + (bank.reg len).val ≤ 2^w →
      (lib j).bounded fuel (readWords w (bank.reg len).val s)) :
    (generate lib fuel cap bank (.call j addr len pc) s).isSome ↔
      (bank.reg len).val ≤ cap ∧ (bank.reg addr).val + (bank.reg len).val ≤ 2^w := by
  let q := (bank.reg len).val
  let x := (bank.reg addr).val
  let vs := readWords w q s
  let rest := drop s (q*w)
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨ha,_,hc,_⟩ := (generate_iff ..).mp hz
    change (if x+q ≤ 2^w then some (.burst x q) else none) = some z.event.action at ha
    split at ha
    · rename_i valid
      rw [← Option.some.inj ha] at hc
      exact ⟨hc,valid⟩
    · contradiction
  · rintro ⟨hq,hx⟩
    obtain ⟨b,n,_,_,out,u,_,he⟩ := (lib j).prefix_run vs (bound hq hx) rest
    let bs := takeBits rest b
    let sg := TeamPrivateCall.sign out
    let event : TeamRAM.Event w := ⟨.burst x q,vs,bs,sg⟩
    refine ⟨⟨event, ⟨pc, bank.reg⟩⟩,(generate_iff ..).mpr ⟨?_,?_,hq,?_⟩⟩
    · change (if x+q ≤ 2^w then some (TeamTranscript.Action.burst (Word := Word w) x q) else none) = some (.burst x q)
      exact ite_eq_left hx
    · change (if vs.length = q then ((lib j).eval fuel vs bs).map _ else none) = _
      simp only [show vs.length = q from readWords_length .., ↓reduceIte]
      rw [show (lib j).eval fuel vs bs = some sg from he]; rfl
    · apply (prefix_append ..).mpr
      refine ⟨readWords_prefix ..,?_⟩
      change Prefix (drop s (TeamBurstProbe.choices vs).length) bs
      simp only [Prefix, bs, prefix_length, choices_length, vs, readWords_length, rest]

/-- An ordinary instruction produces an event precisely when it admits an external action;
invalid and terminal callbacks consume no event choices. -/
theorem native_isSome_iff (lib : Fin a → TeamSite.Macro Q Γ m g) (fuel cap : ℕ)
    (bank : PrivateRAM.LogConfig w p r) (cb : ISA.Callback p r) (s : Supply) :
    (generate lib fuel cap bank (.native cb) s).isSome ↔
      ((TeamOpcode.Exit.native cb).action (macros lib fuel) bank).action.isSome := by
  cases cb <;> simp [generate, TeamOpcode.Exit.action, TeamOpcode.nativeAction, ISA.Callback.action,
    TeamRAM.Instr.action, TeamRAM.Instr.advance, TeamTranscript.Action.extra, probes, readWords, branches]

/-- Any reachable clocked macro gets an event whenever the fetched action exists and
its extra charge fits the cap. The test applies equally to every supplied choice stream. -/
theorem generate_isSome_iff (lib : Fin a → TeamSite.Macro Q Γ m g) (fuel cap : ℕ)
    (bank : PrivateRAM.LogConfig w p r) (out : TeamOpcode.Exit p r a) (s : Supply)
    (bound : ∀ j vs, vs.length ≤ cap → (lib j).bounded fuel (vs : List (Word w))) :
    (generate lib fuel cap bank out s).isSome ↔
      ∃ act, (out.action (macros lib fuel) bank).action = some act ∧ act.extra ≤ cap := by
  cases out with
  | call j addr len pc =>
    rw [call_isSome_iff lib fuel cap bank j addr len pc s (fun h _ => bound _ _ (by simpa using h))]
    by_cases h : (bank.reg addr).val + (bank.reg len).val ≤ 2^w <;>
      simp [TeamOpcode.Exit.action, TeamRAM.Instr.action, TeamTranscript.Action.extra,h]
  | sign =>
    simp [generate, TeamOpcode.Exit.action, TeamRAM.Instr.action, TeamRAM.Instr.advance,
      TeamTranscript.Action.extra, probes, readWords, branches]
  | native cb =>
    rw [native_isSome_iff]
    cases cb <;> simp [TeamOpcode.Exit.action, TeamOpcode.nativeAction, ISA.Callback.action,
      TeamRAM.Instr.action, TeamTranscript.Action.extra]

end TeamSiteEvents

end BorderVNP
end Computability
end OAI

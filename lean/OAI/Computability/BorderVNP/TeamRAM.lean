import OAI.Computability.BorderVNP.TeamTranscript
import OAI.Computability.VPVNP.RAMExecution

/-!
# Adaptive shared-memory instructions and signed paths

A control state in §7.2 contains the program counter and registers. It determines
the next instruction and its address before a probe. A load can choose its next
state from the retrieved word. A private routine reads a consecutive interval,
uses its own branch choices, and returns only its path contribution. This module
relates native execution to local guessed-word runs on these instructions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamRAM

open VPVNP
open VPVNP.BurstRAM (Word Memory)

variable {w : ℕ} {S : Type*}

/-- The integer contribution returned by a subroutine or ordinary sign instruction. -/
inductive Sign where
  | plus | minus | zero
  deriving DecidableEq

/-- Coefficient weight of a single local choice. -/
def Sign.value : Sign → ℤ
  | .plus => 1
  | .minus => -1
  | .zero => 0

/-- A decoded instruction at the current register state. Arithmetic, comparisons and
shifts give a local transition or rejection. An out-of-range burst rejects. Only the
sign is returned from its private run, indexed by the exact binary choices it consumes. -/
inductive Instr (w : ℕ) (S : Type*) where
  | accept | reject
  | localStep (next : S) (sign : Sign)
  | choose (next : Bool → S)
  | load (address : Word w) (next : Word w → S)
  | store (address value : Word w) (next : S)
  | call (address : Word w) (length : ℕ) (run : List (Word w) → List Bool → Option Sign) (next : S)

/-- Persistent external memory operations visible to the distributed validators. -/
def Instr.action : Instr w S → Option (TeamTranscript.Action (Word w))
  | .accept | .reject => none
  | .localStep .. | .choose .. => some (.ordinary none)
  | .load a _ => some (.ordinary (some (a.val, none)))
  | .store a v _ => some (.ordinary (some (a.val, some v)))
  | .call a q _ _ => if a.val + q ≤ 2 ^ w then some (.burst a.val q) else none

/-- Local state and path weight after the claimed probe values and private choices.
Unused choices at deterministic instructions are rejected. A store's previous
word contributes only to its memory record. -/
def Instr.advance : Instr w S → List Bool → List (Word w) → Option (S × Sign)
  | .localStep next sign, [], [] => some (next, sign)
  | .choose next, [b], [] => some (next b, .plus)
  | .load _ next, [], [v] => some (next v, .plus)
  | .store _ _ next, [], [_] => some (next, .plus)
  | .call _ q run next, bits, vs => if vs.length = q then (run vs bits).map (next, ·) else none
  | _, _, _ => none

/-- Old words at the accessed addresses, before executing the instruction. -/
def previous (m : Memory w) : TeamTranscript.Action (Word w) → List (Word w)
  | .ordinary none => []
  | .ordinary (some (a, _)) => [m a]
  | .burst a q => List.ofFn (fun i : Fin q => m (a + i.val))

/-- Only a store changes persistent memory. Consecutive subroutine reads are private input. -/
def afterAction (m : Memory w) : TeamTranscript.Action (Word w) → Memory w
  | .ordinary (some (a, some v)) => Function.update m a v
  | _ => m

/-- A path step retains its branch identity even if another choice yields the same state. -/
structure Event (w : ℕ) where
  /-- External action fetched before the read. -/
  action : TeamTranscript.Action (Word w)
  /-- Claimed previous words, in address order for a burst. -/
  old : List (Word w)
  /-- Exact binary choices consumed by this instruction or its private routine. -/
  choices : List Bool
  /-- Local signed contribution. -/
  sign : Sign

/-- Native execution on the true external memory. The choice tape has one block per
executed instruction, including empty blocks for deterministic transitions. -/
def execute (P : S → Instr w S) : S → Memory w → List (List Bool) → Option (List (Event w))
  | s, _, [] => match P s with | .accept => some [] | _ => none
  | s, m, bits :: rest =>
    match (P s).action with
    | none => none
    | some act =>
      match (P s).advance bits (previous m act) with
      | none => none
      | some (next, sign) => (execute P next (afterAction m act) rest).map fun tail =>
        ⟨act, previous m act, bits, sign⟩ :: tail

/-- Local instruction execution can use guessed words. The fetched action still depends
on the state reached by every preceding branch, read and register update. -/
def Local (P : S → Instr w S) : S → List (Event w) → Prop
  | s, [] => P s = .accept
  | s, e :: es => (P s).action = some e.action ∧
    ∃ next, (P s).advance e.choices e.old = some (next, e.sign) ∧ Local P next es

/-- The previous-word claims agree with chronological shared-memory execution. -/
def Correct (m : Memory w) : List (Event w) → Prop
  | [] => True
  | e :: es => e.old = previous m e.action ∧ Correct (afterAction m e.action) es

/-- Native accepting paths give locally valid transitions, true old words, and exactly
the original choice tape (including the private choices at each call). -/
theorem execute_spec {P : S → Instr w S} {s : S} {m : Memory w} {bits : List (List Bool)}
    {es : List (Event w)} (h : execute P s m bits = some es) :
    Local P s es ∧ Correct m es ∧ es.map Event.choices = bits := by
  induction bits generalizing s m es with
  | nil =>
    cases hp : P s <;> simp [execute, hp] at h
    subst es
    exact ⟨hp, trivial, rfl⟩
  | cons b bs ih =>
    cases ha : (P s).action with
    | none => simp [execute, ha] at h
    | some act =>
      cases hn : (P s).advance b (previous m act) with
      | none => simp [execute, ha, hn] at h
      | some step =>
        obtain ⟨next, sign⟩ := step
        cases ht : execute P next (afterAction m act) bs with
        | none => simp [execute, ha, hn, ht] at h
        | some tail =>
          simp [execute, ha, hn, ht] at h
          subst es
          obtain ⟨hl, hc, hb⟩ := ih ht
          exact ⟨⟨ha, next, hn, hl⟩, ⟨rfl, hc⟩, congrArg (b :: ·) hb⟩

/-- Once the local words have been checked, instruction replay recovers the native
accepting path with its private choice identities. -/
theorem execute_iff {P : S → Instr w S} {s : S} {m : Memory w} {bits : List (List Bool)}
    {es : List (Event w)} : execute P s m bits = some es ↔
      Local P s es ∧ Correct m es ∧ es.map Event.choices = bits := by
  refine ⟨execute_spec, ?_⟩
  rintro ⟨hl, hc, rfl⟩
  induction es generalizing s m with
  | nil => simp [execute, (show P s = .accept from hl)]
  | cons e es ih =>
    obtain ⟨ha, next, hn, hl'⟩ := hl
    obtain ⟨he, hc'⟩ := hc
    rcases e with ⟨act, vs, bits, sign⟩
    change vs = previous m act at he
    subst vs
    simp [execute, ha, hn, ih hl' hc']

/-- Read the claimed old words out of each instruction's portion of a chronological record
array. No previous-word claim can be dropped even when the instruction writes. -/
def Claims : ℕ → List (Event w) → List (TeamRecords.Record (Word w)) → Prop
  | _, [], rs => rs = []
  | t, e :: es, rs =>
    let k := (e.action.accesses t).length
    (rs.take k).map TeamRecords.Record.before = e.old ∧
      Claims (t + (1 + e.action.extra)) es (rs.drop k)

private theorem transcript_action (m : Memory w) (t : ℕ) (act : TeamTranscript.Action (Word w))
    (tail : List (TeamRecords.Access (Word w))) :
    ∃ rs : List (TeamRecords.Record (Word w)), rs.length = (act.accesses t).length ∧
      rs.map TeamRecords.Record.before = previous m act ∧
      TeamRecords.transcript m (act.accesses t ++ tail) =
        rs ++ TeamRecords.transcript (afterAction m act) tail := by
  cases act with
  | ordinary p =>
    cases p with
    | none => exact ⟨[], rfl, rfl, rfl⟩
    | some p =>
      obtain ⟨a, v⟩ := p
      cases v with
      | none =>
        refine ⟨[⟨a, t, m a, m a⟩], rfl, rfl, ?_⟩
        simp [TeamTranscript.Action.accesses, TeamRecords.transcript, TeamRecords.Access.record,
          afterAction, Function.update_eq_self]
      | some v => exact ⟨[⟨a, t, m a, v⟩], rfl, rfl, rfl⟩
  | burst a q =>
    refine ⟨_, ?_, ?_, TeamRecords.transcript_readBurst m a t q tail⟩
    · simp only [List.length_ofFn, TeamTranscript.Action.accesses]
      induction q generalizing a t with
      | zero => rfl
      | succ q ih => simp [TeamRecords.readBurst, ← ih]
    · rw [List.map_ofFn]; rfl

/-- Testing the fetched old-word lists against the canonical records recovers exactly
the adaptive chronological memory condition. -/
theorem claims_transcript_iff (m : Memory w) (t : ℕ) (es : List (Event w)) :
    Claims t es (TeamRecords.transcript m (TeamTranscript.probes Event.action t es)) ↔ Correct m es := by
  induction es generalizing t m with
  | nil => simp [Claims, Correct, TeamTranscript.probes, TeamRecords.transcript]
  | cons e es ih =>
    obtain ⟨rs, hlen, hwords, heq⟩ := transcript_action m t e.action
      (TeamTranscript.probes Event.action (t + (1 + e.action.extra)) es)
    simp only [TeamTranscript.probes, Claims, Correct, heq, ← hlen,
      List.take_left, List.drop_left, hwords, ih, eq_comm]


/-- The only old-word claims passing the local sorted checks are the actual ones,
including at loads which determine future register states and memory addresses. -/
theorem claims_of_history_iff {r h H I : ℕ} {hr : 0 < r} {header : ℕ → Word w}
    {es : List (Event w)} {t : TeamTranscript.History (Event w) (Word w) r h}
    {place : Equiv.Perm (Fin (2 ^ (h + Nat.clog 2 r)))}
    (hv : t.Valid hr H Event.action I header place es)
    (fit : (TeamTranscript.accesses Event.action I header es).length ≤ 2 ^ (h + Nat.clog 2 r)) :
    Claims 1 es (t.records.drop I) ↔ Correct (RAMMemory.initialMemory I header) es := by
  rw [hv.records_eq fit, TeamTranscript.accesses, TeamRecords.transcript_initialization]
  let init := (List.range I).map (fun a => (⟨a, 0, 0, header a⟩ : TeamRecords.Record (Word w)))
  change Claims 1 es ((init ++ _).drop I) ↔ _
  have hlen : init.length = I := by simp [init]
  rw [← hlen, List.drop_left, hlen]
  exact claims_transcript_iff ..

/-- Native execution and local validation have the same signed paths at the team tick bound.
A valid local history determines every guessed word and every sorting and boundary message.
Conversely each native path extends uniquely, retaining its exact ordinary and private
choice tapes and the product of its signed contributions. -/
theorem eventually_execute_iff {ξ : ℝ} (hξ : 0 < ξ) (hξ' : ξ < 3 / 2)
    (P : S → Instr w S) (start : S) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ r : ℕ, ∀ hr : 0 < r, ∀ I : ℕ, I ≤ r * (3 * TeamScales.block ξ n) →
      ∀ (header : ℕ → Word w) (es : List (Event w)) (bits : List (List Bool)),
      (∀ e ∈ es, e.action.extra ≤ TeamScales.width n (1 / 2)) →
      RAMBuckets.cost (fun e => e.action.extra) es ≤ TeamScales.ticks ξ r n →
      let h := Nat.clog 2 (4 * TeamScales.block ξ n)
      ∀ place : Equiv.Perm (Fin (2 ^ (h + Nat.clog 2 r))),
        execute P start (RAMMemory.initialMemory I header) bits = some es ↔
          ∃! t : TeamTranscript.History (Event w) (Word w) r h,
            t.Valid hr (TeamScales.block ξ n) Event.action I header place es ∧
            Local P start es ∧ Claims 1 es (t.records.drop I) ∧ es.map Event.choices = bits ∧
            t.weight (Sign.value ∘ Event.sign) = (es.map (Sign.value ∘ Event.sign)).prod := by
  filter_upwards [TeamScales.eventually_ticks_fit hξ hξ'] with n hcap
  intro r hr I hi header es bits bounded ht h place
  have hc := ht.trans (hcap r hr).le
  have fit := TeamTranscript.accesses_length_le Event.action header es hi
    (hc.trans (Nat.mul_le_mul_left _ (Nat.sub_le ..)))
  obtain ⟨t, hv, hu⟩ := TeamTranscript.existsUnique_history hr h _ _ Event.action I header place es
    bounded hc fit
  constructor
  · intro he
    obtain ⟨hl, hm, hb⟩ := execute_spec he
    exact ⟨t, ⟨hv, hl, (claims_of_history_iff hv fit).mpr hm, hb, hv.weight_eq _⟩,
      fun t' ht' => hu t' ht'.1⟩
  · rintro ⟨t', ⟨hv', hl, hc', hb, _⟩, _⟩
    exact execute_iff.mpr ⟨hl, (claims_of_history_iff hv' fit).mp hc', hb⟩

end TeamRAM

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.TeamPrivateFragment
import OAI.Computability.BorderVNP.TeamRAM

/-!
# Private tape calls in the signed team RAM

A private routine receives the concatenation of the fixed-width binary words it
read. At a signed halt it returns its weight to the outer RAM. The exact list
of branch choices is passed only to that routine.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamPrivateCall

open TeamPrivateTape TeamPrivateFragment VPVNP.RAMTape
open VPVNP.BurstRAM (Word)

variable {Q Γ S : Type*} {w m g d : ℕ}

/-- Replay an exact private choice tape for at most `fuel` native steps, counting
the final halt check. Running out of fuel or bits, or leaving surplus bits, rejects. -/
def evaluate (P : Table Q d) : ℕ → Q → (Fin d → Track) → List Bool → Option (Option Bool × (Fin d → Track))
  | 0, _, _, _ => none
  | f+1, q, t, bits => match P q (heads t) with
    | .halt accept neg => if bits = [] then some (if accept then some neg else none, t) else none
    | .one c => evaluate P f c.next (c.apply t) bits
    | .two l r => match bits with
      | [] => none
      | b :: tail => let c := if b then r else l; evaluate P f c.next (c.apply t) tail

/-- Successful native replay yields an exact bounded path with all private choices. -/
theorem evaluate_spec {P : Table Q d} {fuel q t bits out u}
    (h : evaluate P fuel q t bits = some (out,u)) :
    ∃ n < fuel, Run P n q t bits out u := by
  induction fuel generalizing q t bits with
  | zero => simp [evaluate] at h
  | succ f ih =>
    cases ht : P q (heads t) with
    | halt a s =>
      by_cases hb : bits = []
      · subst bits
        obtain ⟨rfl, rfl⟩ : (if a then some s else none) = out ∧ t = u := by simpa [evaluate, ht] using h
        exact ⟨0, Nat.zero_lt_succ _, .stop ht⟩
      · simp [evaluate, ht, hb] at h
    | one c =>
      obtain ⟨n, hn, hr⟩ := ih (by simpa [evaluate, ht] using h)
      exact ⟨n+1, Nat.succ_lt_succ hn, .one ht hr⟩
    | two l r =>
      cases bits with
      | nil => simp [evaluate, ht] at h
      | cons b bs =>
        obtain ⟨n, hn, hr⟩ := ih (by simpa [evaluate, ht] using h)
        exact ⟨n+1, Nat.succ_lt_succ hn, .two b ht hr⟩

/-- Every native path is accepted by the choice-tape decoder at all sufficient clocks. -/
theorem evaluate_of_run {P : Table Q d} {n q t bits out u} (r : Run P n q t bits out u)
    {fuel : ℕ} (hf : n < fuel) : evaluate P fuel q t bits = some (out,u) := by
  induction r generalizing fuel with
  | stop h => cases fuel <;> simp_all [evaluate]
  | one h _ ih => cases fuel <;> simp_all [evaluate]
  | two b h _ ih => cases fuel <;> simp_all [evaluate]

/-- Little-endian fixed-width encoding of the words supplied to one private call. -/
def inputBits (vs : List (Word w)) : List Bool :=
  vs.flatMap (fun x => List.ofFn (fun i : Fin w => x.val.testBit i.val))

/-- Input preparation uses exactly the advertised word width per probe. -/
theorem inputBits_length (vs : List (Word w)) : (inputBits vs).length = vs.length * w := by
  induction vs with
  | nil => simp [inputBits]
  | cons v vs ih =>
    change (List.ofFn (fun i : Fin w => v.val.testBit i.val) ++ inputBits vs).length = (vs.length+1)*w
    rw [List.length_append, List.length_ofFn, ih, Nat.succ_mul, Nat.add_comm]

/-- Decode the three possible terminal weights. -/
def sign : Option Bool → TeamRAM.Sign
  | none => .zero
  | some false => .plus
  | some true => .minus

/-- Actual finite-alphabet private routine as a RAM instruction. The original outer
register state fixes its address, read length and next state. Private tapes are
unavailable to the resumed RAM. -/
noncomputable def call (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m) (P : TapeTable Q Γ m)
    (entry : Q) (fuel : ℕ) (address : Word w) (len : ℕ) (next : S) : TeamRAM.Instr w S :=
  .call address len (fun vs bits =>
    let t := tracks a (input a.blank digit i (inputBits vs))
    (evaluate (trackTable a P) fuel entry t bits).map (fun result => sign result.1)) next

/-- The RAM's private transition accepts precisely the signed native paths on the
read interval. The resulting outer state is its prescribed continuation. -/
theorem call_advance_iff (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m) (P : TapeTable Q Γ m)
    (entry : Q) (fuel : ℕ) (address : Word w) (len : ℕ) (next : S) (vs : List (Word w))
    (bits : List Bool) (result : TeamRAM.Sign) :
    (call a digit i P entry fuel address len next).advance bits vs = some (next, result) ↔
      vs.length = len ∧ ∃ n < fuel, ∃ o u,
        Run (trackTable a P) n entry (tracks a (input a.blank digit i (inputBits vs))) bits o u ∧
          sign o = result := by
  simp only [call, TeamRAM.Instr.advance]
  split
  · rename_i hl
    rw [and_iff_right hl]
    cases he : evaluate (trackTable a P) fuel entry (tracks a (input a.blank digit i (inputBits vs))) bits with
    | none =>
      simp only [Option.map_none, reduceCtorEq, false_iff]
      rintro ⟨n, hn, o, u, hrun, _⟩
      rw [evaluate_of_run hrun hn] at he
      contradiction
    | some outcome =>
      obtain ⟨o, u⟩ := outcome
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
      constructor
      · intro hs
        obtain ⟨n, hn, hrun⟩ := evaluate_spec he
        exact ⟨n, hn, o, u, hrun, hs⟩
      · rintro ⟨n, hn, o', u', hrun, hs⟩
        have heq := Option.some.inj (he.symm.trans (evaluate_of_run hrun hn))
        exact (congrArg sign (congrArg Prod.fst heq)).trans hs
  · rename_i hl; simp [hl]

end TeamPrivateCall

end BorderVNP
end Computability
end OAI

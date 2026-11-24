import OAI.Computability.VPVNP.EvaluatorTallyLoop
import OAI.Computability.VPVNP.EvaluatorRoutine
import OAI.Computability.VPVNP.EvaluatorDigitRepeat
import OAI.Computability.VPVNP.StructuredStackRuns

/-! # Chronological semantics of a unary evaluator scan

Each iteration may branch. The remaining clock covers the index increment
and every later iteration on each branch. The final cleanup removes the
index accumulated throughout the scan.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorTallyLoop

open RAMTape EvaluatorRoutine

variable {K Q S : Type*} [DecidableEq K]

/-- The two physical stack counters represent the current index and the
number of callbacks still to be invoked. -/
structure TallyBank (remain index : K) (bank : ℕ → ℕ → S → Stacks K) : Prop where
  remainAt : ∀ i r x, bank i r x remain = List.replicate r true
  indexAt : ∀ i r x, bank i r x index = List.replicate i true
  popRemain : ∀ i r x, Function.update (bank i (r+1) x) remain (List.replicate r true) = bank i r x
  pushIndex : ∀ i r x, Function.update (bank i r x) index (true :: bank i r x index) = bank (i+1) r x
  clearIndex : ∀ i x, Function.update (bank i 0 x) index [] = bank 0 0 x

/-- The usual framed bank supplies these equations for any payload bank. -/
theorem TallyBank.of_frame (remain index : K) (hne : remain ≠ index) (base : S → Stacks K) :
    TallyBank remain index (fun i r x =>
      EvaluatorDigitRepeat.frame remain index (base x) (List.replicate r true) (List.replicate i true)) := by
  constructor
  · intro i r x
    simp [EvaluatorDigitRepeat.frame, hne]
  · intro i r x
    simp [EvaluatorDigitRepeat.frame]
  · intro i r x
    simp [EvaluatorDigitRepeat.frame, Function.update_comm hne.symm]
  · intro i r x
    simp [EvaluatorDigitRepeat.frame, List.replicate_succ]
  · intro i x
    simp [EvaluatorDigitRepeat.frame]

/-- Starting with index `i` and `r` remaining marks composes the successive
callback effects in increasing index order. Each callback has its own paths
and may use fewer than `B` instructions on any of them. -/
theorem loop_realizes (remain index : K) (body : Routine K Q) (bank : ℕ → ℕ → S → Stacks K)
    (hb : TallyBank remain index bank) (B : ℕ) (op : ℕ → (S → ℕ) → S → ℕ) (i r : ℕ)
    (hbody : ∀ j left, j + left < i + r → Realizes body (bank j left) (bank j left) B (op j)) :
    Realizes (tallyLoop remain index body) (bank i r) (bank 0 0)
      (r*(B+2)+(i+r)+2) (fun f => (List.range' i r).foldr op f) := by
  induction r generalizing i with
  | zero =>
    intro extra fuel hf x f c hc
    have hs := hb.remainAt i 0 x
    have hlen : (bank i 0 x index).length = i := by rw [hb.indexAt, List.length_replicate]
    have h := loop_count_zero remain index body c (bank i 0 x) hs (fuel-(i+2))
    rw [hlen, hb.clearIndex, show fuel-(i+2)+i+2 = fuel by simp at hf; omega] at h
    exact h.trans (hc x _ (by simp at hf; omega))
  | succ r ih =>
    have hnext := ih (i+1) (fun j left hj => hbody j left (by omega))
    intro extra fuel hf x f c hc
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    have hs : bank i (r+1) x remain = true :: List.replicate r true := by
      rw [hb.remainAt, List.replicate_succ]
    rw [loop_count_succ remain index body c _ _ hs, hb.popRemain, List.range'_succ]
    simp only [List.foldr_cons]
    let rest := r*(B+2)+(i+1+r)+2
    apply hbody i r (by omega) (extra+rest+1) fuel (by
      dsimp [rest]
      simp only [Nat.succ_mul] at hf
      omega)
    intro y k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hpush := (Routine.runs_push index true (bank i r y)).count_eq ((tallyLoop remain index body).count c) k
    rw [hb.pushIndex] at hpush
    exact hpush.trans (hnext extra k (by dsimp [rest] at hk; omega) y f c hc)

end EvaluatorTallyLoop

end VPVNP
end Computability
end OAI

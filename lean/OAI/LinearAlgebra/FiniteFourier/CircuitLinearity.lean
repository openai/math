import OAI.LinearAlgebra.FiniteFourier.Circuit

/-! # Matrix action of a binary linear circuit -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {K I O : Type*} [Semiring K] [Fintype I]

private theorem wire_eq_sum [DecidableEq I] {s : ℕ} (p : Program K I s) (x : I → K) (w : I ⊕ Fin s) :
    Sum.elim x (p.value x) w =
      ∑ i, Sum.elim (Pi.single i 1) (p.value (Pi.single i 1)) w * x i := by
  classical
  induction p with
  | nil =>
    cases w with
    | inl j => simp [Pi.single_apply, ite_mul]
    | inr j => exact j.elim0
  | step p g ih =>
    cases w with
    | inl j => simp [Pi.single_apply, ite_mul]
    | inr j =>
      refine Fin.cases ?_ (fun k => ih (.inr k)) j
      change g.eval _ = ∑ i, g.eval _ * x i
      simp only [BinaryGate.eval, add_mul, mul_assoc, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      rw [← ih g.left, ← ih g.right]

/-- Evaluating a circuit on any input gives the matrix-vector product of its basis
evaluations with that input. -/
theorem Circuit.eval_eq_mulVec {s : ℕ} (p : Circuit K I O s) (x : I → K) :
    p.eval x = p.matrix.mulVec x := by
  classical
  funext o
  change (p.output o).eval _ = ∑ i, (p.output o).eval _ * x i
  cases p.output o with
  | zero => simp [Readout.eval]
  | scaled a w =>
    simp only [Readout.eval, mul_assoc, ← Finset.mul_sum]
    rw [← wire_eq_sum p.program x w]

end FiniteFourier
end LinearAlgebra
end OAI

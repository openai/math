import OAI.Optimization.LinearProgramming.Compression.ProxyOracle
import OAI.Optimization.LinearProgramming.Lattice.Bisection

/-! The affine and homogeneous forms of the computed proxy vector used by both
realized numerical machines and the canonical lattice-word service. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace DyadicRAM
open OAI.Optimization.LinearProgramming.Lattice
open scoped BigOperators

noncomputable def cachedForm {n : ℕ} (fuel prec : ℕ) (mag : ℕ → ℚ) (row : Fin (n+1) → ℤ) : ℝ :=
  (row (Fin.last n):ℝ) + ∑ i : Fin n, (row i.castSucc:ℝ) *
    logProxyValue prec (mag i) (logProxyNumerator fuel prec (mag i))

noncomputable def cachedReply {n : ℕ} (fuel prec : ℕ) (mag : ℕ → ℚ)
    (row : Fin (n+1) → ℤ) : Bool := decide (0 ≤ cachedForm fuel prec mag row)

def coefficientBudget {n : ℕ} (A : ℤ) (row : Fin (n+1) → ℤ) : Prop :=
  |row (Fin.last n)| + ∑ i : Fin n, |row i.castSucc| ≤ A

noncomputable def cacheHomogeneous {n : ℕ} (fuel prec : ℕ) (mag : ℕ → ℚ) : Fin (n+1) → ℝ :=
  Fin.snoc (fun i : Fin n => logProxyValue prec (mag i) (logProxyNumerator fuel prec (mag i))) 1

theorem cachedReply_form {n : ℕ} (fuel prec : ℕ) (mag : ℕ → ℚ) (row : Fin (n+1) → ℤ) :
    cachedReply fuel prec mag row=true ↔ 0 ≤ formValue row (cacheHomogeneous fuel prec mag) := by
  have value : formValue row (cacheHomogeneous fuel prec mag) = cachedForm fuel prec mag row := by
    rw [formValue,Fin.sum_univ_castSucc]
    simp [cachedForm,cacheHomogeneous,add_comm]
  rw [value]
  unfold cachedReply
  exact ⟨fun h => @of_decide_eq_true _ _ h, fun h => @decide_eq_true _ _ h⟩

end DyadicRAM
end Compression
end LinearProgramming
end Optimization
end OAI

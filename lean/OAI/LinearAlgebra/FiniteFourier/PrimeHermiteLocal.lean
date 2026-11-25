import OAI.LinearAlgebra.FiniteFourier.PrimeHermiteOps
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Pointwise linear circuits on a bank of work rows -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {K I O B : Type*} [CommSemiring K] [Fintype I] [Fintype B]

/-- Each label can run its own independent circuit, with the costs added over the labels. -/
theorem realizesOp_pointwise {F : B → (I → K) → O → K} {s : B → ℕ}
    (h : ∀ b, RealizesOp (F b) (s b)) :
    RealizesOp (fun (x : I × B → K) (p : O × B) => F p.2 (fun i => x (i, p.2)) p.1)
      (∑ b, s b) := by
  classical
  choose M hM hF using h
  refine ⟨Matrix.blockDiagonal M, RealizableAtMost.blockDiagonal_family hM, ?_⟩
  intro x
  funext ⟨o, b⟩
  change _ = F b (fun i => x (i, b)) o
  rw [← hF b (fun i => x (i, b))]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.blockDiagonal_apply, ite_mul]

/-- Applying an arbitrary matrix at each label costs at most the number of
labels times the size of one matrix. -/
theorem realizesOp_pointwise_matrix [Fintype O] (M : B → Matrix O I K) :
    RealizesOp (fun (x : I × B → K) (p : O × B) => (M p.2).mulVec (fun i => x (i, p.2)) p.1)
      (Fintype.card B * Fintype.card I * Fintype.card O) := by
  have h (b : B) : RealizesOp ((M b).mulVec) (Fintype.card O * Fintype.card I) :=
    ⟨M b, realizableAtMost_card_mul_card _, fun _ => rfl⟩
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using realizesOp_pointwise h

/-- A family of arbitrary linear maps on the work rows has cost linear in the label count. -/
theorem realizesOp_pointwise_linear [Fintype O] (L : B → (I → K) →ₗ[K] (O → K)) :
    RealizesOp (fun (x : I × B → K) (p : O × B) => L p.2 (fun i => x (i, p.2)) p.1)
      (Fintype.card B * Fintype.card I * Fintype.card O) := by
  classical
  simpa only [LinearMap.toMatrix'_mulVec] using
    (realizesOp_pointwise_matrix (fun b => LinearMap.toMatrix' (L b)))

end FiniteFourier
end LinearAlgebra
end OAI

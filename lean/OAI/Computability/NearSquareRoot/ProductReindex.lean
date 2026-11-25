import OAI.Computability.NearSquareRoot.ProductMatrixLayers
import OAI.Computability.NearSquareRoot.PrecisionButterflyMatrix

/-! # Moving a rounded matrix pass between address layouts -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ProductRecovery

open Matrix WithLp FixedPoint SynchronizedPadding ProductMatrixLayers
noncomputable section

variable {α β : Type} [Fintype α] [Fintype β]
variable {k : ℕ}

/-- Pull an array indexed by a structured coordinate back to its tape address. -/
def pull (e : α ≃ β) : EuclideanSpace ℂ β ≃ₗᵢ[ℂ] EuclideanSpace ℂ α :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm

theorem pull_apply (e : α ≃ β) (x : EuclideanSpace ℂ β) (i : α) :
    pull e x i = x (e i) := rfl

theorem pull_recordArray (e : α ≃ β) (r : β → Record k) :
    pull e (recordArray r) = recordArray (r ∘ e) := rfl

variable [DecidableEq α] [DecidableEq β]

theorem unitary_reindex (e : α ≃ β) (M : Square β) (h : Mᴴ * M = 1) :
    (M.submatrix e e)ᴴ * M.submatrix e e = 1 := by
  rw [conjTranspose_submatrix, submatrix_mul_equiv, h, submatrix_one_equiv]

theorem pull_matrix (e : α ≃ β) (M : Square β) (h : Mᴴ * M = 1) (x : EuclideanSpace ℂ α) :
    pull e (matrixIsometry M h (pull e.symm x)) =
      matrixIsometry (M.submatrix e e) (unitary_reindex e M h) x := by
  apply WithLp.ofLp_injective
  change (M *ᵥ (ofLp x ∘ e.symm)) ∘ e = M.submatrix e e *ᵥ ofLp x
  rw [submatrix_mulVec_equiv]

/-- One local roundoff certificate transports unchanged across an address equivalence.
Both the working-range hypothesis and the observed error use the full array norm. -/
theorem roundoff_reindex (e : α ≃ β) (M : Square β) (h : Mᴴ * M = 1)
    (apply : (β → Record k) → (β → Record k)) {B δ : ℝ}
    (err : ∀ r, ‖recordArray r‖ ≤ B →
      ‖recordArray (apply r) - matrixIsometry M h (recordArray r)‖ ≤ δ)
    (r : α → Record k) (hr : ‖recordArray r‖ ≤ B) :
    ‖recordArray (apply (r ∘ e.symm) ∘ e) -
        matrixIsometry (M.submatrix e e) (unitary_reindex e M h) (recordArray r)‖ ≤ δ := by
  rw [← pull_recordArray, ← pull_matrix e M h, ← map_sub, LinearIsometryEquiv.norm_map]
  apply err
  change ‖pull e.symm (recordArray r)‖ ≤ B
  rwa [LinearIsometryEquiv.norm_map]

/-- Pull one actual normalized butterfly pass back along any selected-bit split
of the physical address. The row coordinate records all spectator bits. -/
theorem record_butterfly_reindex (e : α ≃ β × Bool) (hk : 1 ≤ k)
    (hcard : Fintype.card α ≤ 2^k) (r : α → Record k)
    (hr : ‖recordArray r‖ ≤ (2 : ℝ)^(13*k)) :
    ‖recordArray (fun a =>
      normalizedBranch k (e a).2 (r (e.symm ((e a).1,false)))
        (r (e.symm ((e a).1,true))) (butterflyCoefficient k)) -
        matrixIsometry ((butterflyMatrix β).submatrix e e)
          (unitary_reindex e _ (butterflyMatrix_unitary β)) (recordArray r)‖ ≤
            1 / (2 : ℝ)^(50*k) := by
  exact roundoff_reindex e _ (butterflyMatrix_unitary β) _ (fun x hx =>
    record_butterfly_error β hk ((Fintype.card_congr e).symm.le.trans hcard) x hx) r hr

end
end ProductRecovery

end NearSquareRoot
end Computability
end OAI

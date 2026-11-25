import OAI.LinearAlgebra.SpectralBooks.GeometricRestriction
import OAI.LinearAlgebra.SpectralBooks.IncrementRestriction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The common-label comparison over arbitrary ground fields

The source and target have coefficients obtained by counting compatible labels.
Base change commutes with this presentation, so the degeneration over the
algebraic closure concerns the scalar extensions of the original two tensors.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Classical

theorem Crossing.map_basisTensor {K E I J : Type*} [CommSemiring K] [CommSemiring E]
    [Fintype I] [Fintype J] {A : I → Type*} (f : K →+* E) (a : J → ∀ i, A i) (x : ∀ i, A i) :
    f (basisTensor (F := K) a x) = basisTensor (F := E) a x := by
  simp [basisTensor]

/-- Over the algebraic closure the base-changed target is in the fixed-format
closure of restrictions of the base-changed source. -/
theorem commonLabel_geometricRestriction (K : Type*) [Field K] (q k m : ℕ) :
    (fun b ↦ algebraMap K (AlgebraicClosure K)
      (Crossing.basisTensor (F := K) (incrementTargetBasis q k m) b)) ∈
      affineZariskiClosure {Y | Crossing.IsRestriction Y (fun a ↦ algebraMap K (AlgebraicClosure K)
        (Crossing.basisTensor (F := K)
          (incrementSourceBasis q k m (2 * (k + 1) * (q - 1) + 1)) a))} := by
  simpa only [Crossing.map_basisTensor] using commonLabel_borderRestriction (AlgebraicClosure K) q k m

/-- Comparison at every spectral point of the original field, including all finite fields. -/
theorem commonLabel_value_le (K : Type*) [Field K] (q k m : ℕ)
    (φ : normalizedSpectrum ((· ≤ ·) : SiteTensor.TensorClass.{0} (IncrementSite k m) K → _ → Prop)) :
    SiteTensor.coeffValue φ (Crossing.basisTensor (F := K) (incrementTargetBasis q k m)) ≤
      SiteTensor.coeffValue φ (Crossing.basisTensor (F := K)
        (incrementSourceBasis q k m (2 * (k+1) * (q-1) + 1))) :=
  SiteTensor.coeffValue_le_of_geometric_restriction (E := AlgebraicClosure K) φ _ _
    (commonLabel_geometricRestriction K q k m)

end SpectralBooks
end LinearAlgebra
end OAI

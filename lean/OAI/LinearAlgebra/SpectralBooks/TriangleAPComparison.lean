import OAI.LinearAlgebra.SpectralBooks.TriangleAPDiagonal
import OAI.LinearAlgebra.SpectralBooks.TriangleAPDegeneration
import OAI.LinearAlgebra.SpectralBooks.RestrictionClosure

/-! # The comparison between the triangle of wires and the common pair of labels -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open SiteTensor

/-- The pair diagonal is a degeneration of the triangle of wires of dimension `2r`. -/
theorem diagonal_mem_triangleWireClosure (K : Type*) [Field K] [Infinite K] (r : ℕ) :
    (Raw.diagonal (Fin 3) K (Fin r × Fin r)).coeff ∈
      affineZariskiClosure {Y | Crossing.IsRestriction Y
        (Crossing.basisTensor (F := K) (triangleWireTerm (2*r)))} :=
  mem_restrictionClosure_of_isRestriction (diagonal_restricts_triangleAPTensor K r)
    (triangleAPTensor_mem_restrictionClosure K (2*r))

/-- Each ground-field spectral point values the common pair of labels at most
as highly as the three wires of twice the label dimension. -/
theorem triangleDiagonal_value_le (K : Type*) [Field K] (r : ℕ)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop)) :
    coeffValue φ (Raw.diagonal (Fin 3) K (Fin r × Fin r)).coeff ≤
      coeffValue φ (Crossing.basisTensor (F := K) (triangleWireTerm (2*r))) :=
  (φ.2.2.2.2.2 _ _ (show ofCoeffs (Raw.diagonal (Fin 3) K (Fin r × Fin r)).coeff ≤
    ofCoeffs (triangleAPTensor K (2*r)) from diagonal_restricts_triangleAPTensor K r)).trans
    (triangleAPTensor_value_le_wire K (2*r) φ)

end SpectralBooks
end LinearAlgebra
end OAI

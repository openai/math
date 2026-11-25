import OAI.LinearAlgebra.SpectralBooks.BorderCircuitShapes
import OAI.LinearAlgebra.SpectralBooks.BorderBaseChange

/-! # Scalar extension for degree-component border circuits -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MvPolynomial

private theorem circuitCoefficientVectors_eq_image (K L σ : Type*) [Field K] [Field L] [Algebra K L]
    (d s : ℕ) :
    circuitCoefficientVectors L σ d s = polynomialFamilyImage L (@circuitShapeCoordinates σ K _ s d) := by
  ext v
  exact mem_circuitCoefficientVectors_iff (K := K)

/-- Over an infinite ground field, testing membership in the Zariski closure of bounded-size
degree-component circuit outputs gives the same answer after any field extension. -/
theorem circuitClosure_map_iff {K L σ : Type*} [Field K] [Field L] [Algebra K L] [Infinite K]
    (d s : ℕ) (f : MvPolynomial σ K) :
    (degreeCoefficientVector d (MvPolynomial.map (algebraMap K L) f) ∈
      zeroLocus L (vanishingIdeal L (circuitCoefficientVectors L σ d s))) ↔
    (degreeCoefficientVector d f ∈ zeroLocus K (vanishingIdeal K (circuitCoefficientVectors K σ d s))) := by
  have hmap : degreeCoefficientVector d (MvPolynomial.map (algebraMap K L) f) =
      algebraMap K L ∘ degreeCoefficientVector d f := by
    funext m
    exact coeff_map _ _ _
  rw [hmap, circuitCoefficientVectors_eq_image K L, circuitCoefficientVectors_eq_image K K]
  exact mem_polynomialFamilyClosure_baseChange_iff L _ _

end SpectralBooks
end LinearAlgebra
end OAI

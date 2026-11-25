import OAI.Hierarchy.MatrixBound
import OAI.LinearAlgebra.SpectralBooks.GaussianNumeric

namespace OAI
/-! # The exact Gaussian constant and its certified rational lower bound -/

namespace Hierarchy

open MatrixMultiplication LinearAlgebra.SpectralBooks

/-- The matrix bound uses the formal scalar-arithmetic exponent of square multiplication. -/
theorem square_exponent_of_prime_flats (flats : UnboundedPrimeFieldFlats)
    (F : Type*) [Field F] :
    2 * Real.exp (stdNormalQuantile (2 / 3) ^ 2 / 2) ≤ formalOmega F 1 1 1 ∧
    (1097 : ℝ) / 500 < formalOmega F 1 1 1 := by
  have exactBound := (matrix_exponents_of_prime_flats flats F).1
  exact ⟨exactBound, lt_of_lt_of_le gaussianSquareExponent_gt_2194 exactBound⟩


end Hierarchy

end OAI

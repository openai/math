import OAI.Hierarchy.PrimeFlats
import OAI.LinearAlgebra.SpectralBooks.GaussianNumeric

namespace OAI
namespace LinearAlgebra.SpectralBooks

/-- The Gaussian lower bound for square matrix multiplication over a field. -/
theorem gaussian_le (F : Type*) [Field F] :
    2 * Real.exp (stdNormalQuantile (2 / 3) ^ 2 / 2) ≤ formalOmega F 1 1 1 :=
  formalOmega_gaussian_square_lower_bound
    (Hierarchy.gaussianMatrixTest_of_prime_flats Hierarchy.prime_flats F)

/-- The rational lower bound for the same square exponent. -/
theorem rational_le (F : Type*) [Field F] : (1097 : ℝ) / 500 ≤ formalOmega F 1 1 1 :=
  gaussianSquareExponent_gt_2194.le.trans (gaussian_le F)

end LinearAlgebra.SpectralBooks
end OAI

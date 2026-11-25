import OAI.Hierarchy.SquareExponent
import OAI.LinearAlgebra.SpectralBooks.DivisionExponent

namespace OAI
/-! # The same square bound for formal programs with division -/

namespace Hierarchy
open LinearAlgebra.SpectralBooks

/-- Reuse square division elimination for admissible formal scalar programs.
The arithmetic lower bound thus applies over finite ground fields as well. -/
theorem division_exponent_of_prime_flats (flats : UnboundedPrimeFieldFlats) (F : Type*) [Field F] :
    2*Real.exp (stdNormalQuantile (2/3)^2/2)≤divisionOmega F 1 1 1 ∧
    (1097:ℝ)/500<divisionOmega F 1 1 1 := by
  rw [divisionOmega_square_eq_formalOmega]
  exact square_exponent_of_prime_flats flats F


end Hierarchy

end OAI

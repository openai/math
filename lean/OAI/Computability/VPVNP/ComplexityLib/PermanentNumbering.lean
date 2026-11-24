import OAI.Computability.VPVNP.ComplexityLib.Family
import OAI.Computability.VPVNP.PermanentPadding
import Complexity.Computability.Circuit.Arithmetic.Determinant

/-! # Row-major numbering of the generic permanent -/

namespace OAI
namespace Computability
namespace VPVNP

namespace ComplexityLib

open Cslib.Circuits.Arithmetic

/-- Numbering the entries of the project's generic matrix in row-major order gives
complexitylib's permanent family, including the member at dimension zero. -/
theorem numbered_permanent (F : Type*) [Field F] :
    numberedFamily (permanentPolynomial F) (fun _ => finProdFinEquiv) = permFamily F := by
  simp only [numberedFamily, permFamily, permanentPolynomial, genericMatrix, Matrix.permanent,
    Matrix.of_apply, map_sum, map_prod, MvPolynomial.rename_X]

end ComplexityLib

end VPVNP
end Computability
end OAI

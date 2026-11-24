import Complexity.Computability.Circuit.Arithmetic.Permanent
import OAI.Computability.VPVNP.ComplexityLib.PermanentNumbering
import OAI.Computability.VPVNP.ComplexityLib.VNPTransport
import OAI.Computability.VPVNP.PermanentHardness

/-! # Valiant's completeness theorem for the generic permanent

Ryser's formula supplies the Boolean-sum verifier over every field. The
permanent reduction uses the inverse of two for its occurrence gadgets.
-/

namespace OAI
namespace Computability
namespace VPVNP

/-- The generic permanent belongs to VNP over every field. Numbering its matrix
entries in row-major order gives the family computed by the Ryser verifier. -/
theorem permanent_isVNP (F : Type*) [Field F] : IsVNP (permanentPolynomial F) := by
  apply (ComplexityLib.numbered_mem_VNP_iff (permanentPolynomial F) (fun _ => finProdFinEquiv)).mp
  rw [ComplexityLib.numbered_permanent]
  exact Cslib.Circuits.Arithmetic.permFamily_mem_VNP

/-- Over every field of characteristic different from two, the generic permanent
belongs to VNP and every VNP family is a p-projection of it. -/
theorem permanent_vnpComplete (F : Type*) [Field F] (q : ℕ) [CharP F q] (hq : q ≠ 2) :
    VNPComplete (permanentPolynomial F) :=
  ⟨permanent_isVNP F, fun _ _ g hg => pProjects_permanent_of_isVNP q hq g hg⟩

end VPVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.DiagonalNativeCoreDirectory
import OAI.Computability.BorderVNP.DiagonalPositiveHeaderSyntax
import OAI.Computability.BorderVNP.CubePhysicalDeclarationWords

/-! # The actual profile and cube declaration of a jointly prepared row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.CoreDirectory

open Crossing TeamContraction.JointHeader

variable {D n d blocks b h K s r : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
    (B : CoreDirectory N n d blocks b h K r)

/-- The pinned selectors determine the unique physical cube declaration.
The preparation supplies its original profile verbatim. Each proposed report
claim subsequently overwrites the placeholder subtotal digits. -/
def issuedHeader {reserve dim digits : ℕ} (profile : Fin reserve → Bool) (v : B.Route s × B.Bank) :
    PositiveFields reserve n d (declarationCap n d blocks b h s) (r+1) dim digits :=
  ⟨profile,broadcast b s v.1.val.1,fun _ => false⟩

end Cube.Physical.NativeAssignments.CoreDirectory

end BorderVNP
end Computability
end OAI

import OAI.Hierarchy.TaggedWireNamedAperture
import OAI.Hierarchy.TaggedWireTurnData

namespace OAI
/-! # Absolute offsets in the gathered native turn words -/
noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open scoped Classical
variable {S n m h : ℕ} (old : Fin n→Chord S) (edge : Fin m→Chord S)
    (route : Fin n→List (Fin m)) (bits : Fin n→ℕ) (ord : Fin h≃Σi,Fin (route i).length)

/-- The occupied prefix of this row among the active rows of the same
physical chord. It is independent of the two end polarities. -/
def datedBase {K n : ℕ} (ends : Fin n→Chord K) (width : Fin n→ℕ) (i : Fin n) : ℕ :=
  TaggedShorterCommonScan.earlier (NamedAperture.key ends) width i.val (NamedAperture.key ends i)

/-- The dated comparison names a complete gathered chord, so its start also
includes the prefix of previous active rows with the same chord. -/
def datedStart (i : Fin n) (ref : TurnRef) :=
  refRole route (fun a _=>datedBase old bits a) (fun a _=>datedBase edge (routeLoad route bits) a) i ref+
    refStart route bits ord i ref


end Hierarchy.WireTelescope
end

end OAI

import OAI.Hierarchy.DescentSharedLeafImage
import OAI.Hierarchy.DescentActorHeaderRAM

namespace OAI
/-! # Publishing one physical header over every surviving high-block lane -/
namespace Hierarchy.DescentActorRaster.Headers
open DescentPackedZip DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w H a G M : ℕ}
theorem broadcast_header (start : ℕ) (R : DescentSharedLeafLookup.Header) (m : Memory w)
    (rank : Fin H→Cell a) (readable : DescentSharedLeafLookup.Readable R 1 H G M a w start)
    (fixed : DescentSharedLeafLookup.Fixed R 1 H G M a m)
    (read : ∀v,m (R.ranks.base+v.val)=((rank v).val:Word w)) :
    Source (DescentSharedLeafLookup.source R (0:Fin 1)) (fun v (_ : Fin G)=>rank v) M m :=by
  apply DescentSharedLeafLookup.repeated_source R start m readable fixed (fun v _=>rank v)
  intro v j
  have ej : j=0:=Subsingleton.elim ..
  simpa [ej] using read v

end
end Hierarchy.DescentActorRaster.Headers

end OAI

import OAI.Hierarchy.DescentOrdinaryRasterRun
import OAI.Hierarchy.DescentVenueQuantityPrice

namespace OAI
/-! # Instruction and clock counts of the two real ordinary census planes -/
namespace Hierarchy.DescentOrdinaryRasterReturn
open DescentSixParty.Chronology DescentSIMDLookup DescentVenueQuantityPlanes DescentStaticWordColumn
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
def fee (d:Dims):=(4+10*d.hosts+7*(15*(d.hosts+1)))+DescentVenueQuantityPlanes.fee d+
  DescentVenueQuantityPlanes.fee (actor d)

theorem billed (d:Dims)(B:Sources)(base w:ℕ)(old:0<d.oldLanes)(new:0<d.lanes)(blocks:0<d.blocks):
    (phase d B base w).ticks+7*names (phase d B base w).program≤fee d:=by
  have a:=DescentVenueQuantityPlanes.billed d (fund d B base) w old new blocks
  have b:=DescentVenueQuantityPlanes.billed (actor d) (seen d B base) w old new blocks
  simp only [phase,NativePhase.seq,identityColumn,names_seq,names_mount,fee]
  omega

end
end Hierarchy.DescentOrdinaryRasterReturn

end OAI

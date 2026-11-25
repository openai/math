import OAI.Hierarchy.DescentDatedMaterialPhase
import OAI.Hierarchy.DescentPhysicalSignedLayout
import OAI.Hierarchy.DescentDatedMeter

namespace OAI
/-! The original return tables use exactly the padded low alphabet of the issued signed rows. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentHostDegree
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
variable {F P:Type} [Field F] (v:PhysicalOrdinary F P)

theorem issued_launch_sites :
    DepotRAM.Material.Route.Projection.launchSites (v.ticket.depotShape v.short).blocks
        v.materialPitch=v.withIssuedSigned.signed.lowSites :=by
  change 2*2^v.k*(((2^(v.k+1)-1)*(2^packExponent 20 v.stage.Δ+2))/(2*2^v.k-1))=
    2^(v.k+1)*(2^packExponent 20 v.prior.placement.degree+2)
  have stair:2*2^v.k=2^(v.k+1):=by rw [pow_succ,Nat.mul_comm]
  rw [stair,(Dated.Meter.ticket_shape v.ticket).2]
  have pos:0<2^(v.k+1)-1:=by have:=Nat.one_lt_two_pow' v.k;omega
  rw [Nat.mul_comm (2^(v.k+1)-1) _,Nat.mul_div_cancel _ pos]

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

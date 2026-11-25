import OAI.Hierarchy.DescentContactOutputPrice
import OAI.Hierarchy.DescentContactOutputFits

namespace OAI
/-! # Bounded native contact date from the original typed fields and the actual preceding calendar -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentSIMDLookup DescentPackedZip DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable (A : Shape) (donorStart first : ℕ) {w : ℕ}
local notation "D" => A.donor
local notation "earlier" => (D).markers donorStart A.shapes A.markerBits
variable (u : DescentContactSenderDate.Prior A.donor.degree A.donor.lows A.donor.cap A.donor.n A.donor.residual)
variable (r : A.donor.Space donorStart u w) (past : (A.donor.markers donorStart A.shapes A.markerBits).endAddress≤first) (room : A.endAddress first<2^w)
variable (batch : 0<A.batch) (blocks : 0<A.blocks)

include past in
theorem older : (D).endAddress donorStart≤first:=by
  obtain ⟨s,t,v,h,i⟩:=(earlier).ordered
  exact s.trans (t.trans (v.trans (h.trans (i.trans past))))

def actualPhase : NativePhase w:=
  A.issuedPhase donorStart first u (A.older donorStart first past) r room batch blocks
    (A.fieldsAt_fits donorStart first u r past room)

include r past room batch blocks in
theorem actual (m : Memory w) :
    (A.issuedProgram donorStart first u w).Exec m (A.issuedImage donorStart first u m) (A.issuedTicks donorStart first u) ∧
    CheapCode (A.issuedProgram donorStart first u w) ∧
    ∀z,z<first ∨ A.endAddress first≤z→A.issuedImage donorStart first u m z=m z:=
  A.issued_any donorStart first u (A.older donorStart first past) r room batch blocks
    (A.fieldsAt_fits donorStart first u r past room) m

include r past room batch blocks in
theorem actual_field (m : Memory w) (oldBatch : 0<(D).batch) (size : (D).groups=A.groups*A.blocks)
    (values : Fin A.sockets→Fin 4→Fin A.sparseHosts→Fin (D).groups→Cell A.metaBits)
    (seen : ∀q f,Source (A.fieldsAt donorStart first u q f) (values q f) (D).batch (A.held donorStart first u m))
    (q : Fin A.sockets) (f : Fin 4) (x : Fin A.blocks) :
    (A.fieldExpr first x q f).Fits w (A.endAddress first) ∧ Source (A.fieldExpr first x q f)
      (fun h g=>values q f h (Fin.cast size.symm (finProdFinEquiv (g,x)))) A.batch (A.issuedImage donorStart first u m):=by
  have h:=A.issued donorStart first u (A.fieldsAt donorStart first u) room batch blocks
    (A.fieldsAt_fits donorStart first u r past room) m oldBatch size values seen q f x
  exact ⟨⟨h.1,trivial⟩,h.2⟩

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI

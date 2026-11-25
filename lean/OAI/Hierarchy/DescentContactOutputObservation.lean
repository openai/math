import OAI.Hierarchy.DescentContactOutputIssued
import OAI.Hierarchy.DescentContactCastInputs

namespace OAI
/-! # All four projected operand values from the attained original contact measurements -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentSIMDLookup DescentPackedZip DescentContactCoordinateJoint
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable (A : Shape) (donorStart first : ℕ) {w : ℕ}
local notation "D" => A.donor
local notation "M" => (D).batch
local notation "t" => A.metaBits
local notation "B" => (D).fieldBits
local notation "R" => 2^Nat.clog 2 ((D).degree+2)
local notation "C" => (D).markers donorStart A.shapes A.markerBits
variable (u : DescentContactSenderDate.Prior A.donor.degree A.donor.lows A.donor.cap A.donor.n A.donor.residual)
variable (r : A.donor.Space donorStart u w) (past : (A.donor.markers donorStart A.shapes A.markerBits).endAddress≤first) (room : A.endAddress first<2^w)
variable (batch : 0<A.batch) (blocks : 0<A.blocks) (old : 0<A.donor.batch) (lanes : A.donor.groups=A.groups*A.blocks)

include r past room batch blocks old in
/-- The source words in RawRead are the numerical mounted marker, one original sender,
the raw receiving shape, the two attained old halo digits, and the actual late count. -/
theorem projected_indicators (m : Memory w) (x : ∀q : Fin A.sockets,RawIndicators A q)
    (attained : ∀q,A.RawRead donorStart first u q (x q) (DescentContactMaskShape.result (D) donorStart first u m))
    (requestFits : ∀q j h g,A.request q*((x q).indicators.used j h g).val<2^B)
    (coordinateFits : ∀q s j h g,number R (((x q).indicators.shape s j h g).val)
      (((x q).indicators.halo s j h g).val)<2^t)
    (q : Fin A.sockets) (f : Fin 4) (block : Fin A.blocks) :
    (A.fieldExpr first block q f).Fits w (A.endAddress first) ∧
    Source (A.fieldExpr first block q f) (fun h g=>(x q).indicators.output f h
      (Fin.cast lanes.symm (finProdFinEquiv (g,block)))) A.batch (A.issuedImage donorStart first u m):=by
  let oldImage:=DescentContactMaskShape.result (D) donorStart first u m
  obtain ⟨_,_,_,_,priorEnd,projEnd⟩:=A.cuts first
  have enough:=projEnd.trans_lt room
  apply A.actual_field donorStart first u r past room batch blocks m old lanes
    (fun q=>(x q).indicators.output) _ q f block
  intro j i
  obtain ⟨bases,issued⟩:=A.inputs_of_raw donorStart first u j (x j) oldImage (attained j) (priorEnd.trans_lt enough)
  exact A.fields_read donorStart first u j (x j).indicators (A.halos first oldImage) bases enough issued
    (requestFits j) (coordinateFits j) i

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI

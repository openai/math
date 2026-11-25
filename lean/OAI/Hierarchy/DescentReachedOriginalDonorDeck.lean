import OAI.Hierarchy.DescentResetOriginalDonorMemory
import OAI.Hierarchy.DescentOriginalDonorDenseRead

namespace OAI
/-! The measured previous signed-slot fields in the dense original-number bank. -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentContactDonorFront DescentContactMaskShape DescentContactProbePitch DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentResetSignedHaloMatrix DescentPackedChildNeighbor.SIMD
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (A : Shape) (donorStart first : ℕ) {w k : ℕ}
set_option quotPrecheck false
local notation "D" => A.donor
local notation "H" => (D).hosts
local notation "J" => (D).groups
local notation "M" => (D).batch
local notation "N" => (D).lows*(2*(D).cap)
local notation "F" => DescentOldContactSender.count (D).degree (D).lows (D).cap (D).n (D).residual
local notation "b" => (D).fieldBits
local notation "C" => (D).markers donorStart A.shapes A.markerBits
local notation "S₀" => (D).sender donorStart
variable (u : DescentContactSenderDate.Prior A.donor.degree A.donor.lows A.donor.cap A.donor.n A.donor.residual)
variable (board : NonlinearExpanders.Graph A.donor.n k) (front : A.donor.Space donorStart u w)
variable (markerEnd : (A.donor.markers donorStart A.shapes A.markerBits).endAddress<2^w) (pack : A.donor.batch*max (A.donor.fieldBits*8) A.markerBits≤w/2)
local notation "markerSpace" => (D).markerSpace donorStart A.shapes A.markerBits u front markerEnd pack
variable (xs : Fin A.donor.hosts→Fin A.donor.groups→Fin (DescentOldContactSender.count A.donor.degree A.donor.lows A.donor.cap A.donor.n A.donor.residual)→Cell A.donor.fieldBits) (next : Fin A.donor.hosts→Fin A.donor.degree→Option (Fin A.donor.hosts))
    (raw : Fin A.donor.lows→Fin (2*A.donor.cap)→Fin A.donor.hosts→Fin A.donor.groups→Cell A.donor.fieldBits)
local notation "marks" => (D).sensorValue donorStart xs next raw
local notation "ys" => (D).boardValues xs
local notation "shelf" => (D).halo donorStart u.routes.roster
local notation "endM" => A.marker first
local notation "W₀" => DescentContactMaskShape.massEnd D first
local notation "size" => H*chunks J M

variable (initial postTrunk : Memory w) (acquired : (A.donor.sender donorStart).Before u xs next raw initial)
    (jobs : (A.donor.sender donorStart).Packed w) (viewWidth : A.donor.batch*max (A.donor.fieldBits*(A.donor.markers donorStart A.shapes A.markerBits).oldFields) (A.donor.markers donorStart A.shapes A.markerBits).viewBits≤w/2)
    (afterMarkers : (A.donor.markers donorStart A.shapes A.markerBits).endAddress≤first) (space : A.marker first+A.donor.hosts*chunks A.donor.groups A.donor.batch<2^w)
    (keys : DescentResetLocalRoster.rootSlots A.donor.residual (2^A.donor.n)*(2^A.donor.n+2^A.donor.height)<2^A.donor.fieldBits)
    (countWidth : A.donor.batch*max (A.donor.fieldBits*(A.donor.lows*(2*A.donor.cap)+1)) A.donor.fieldBits≤w/2) (haloWidth : A.donor.degree+2<2^A.donor.cargoBits)
local notation "before" => (D).memory donorStart u initial
local notation "original" => (D).result donorStart A.shapes A.markerBits u board front markerEnd pack initial
local notation "out" => DescentContactMaskShape.result D donorStart first u postTrunk
variable (kept : ∀addr,addr<(A.donor.markers donorStart A.shapes A.markerBits).endAddress→postTrunk addr=(A.donor.result donorStart A.shapes A.markerBits u board front markerEnd pack initial) addr)

variable (sel short : ℕ) (shape : A.donor.groups=A.groups*A.blocks)
local notation "panels" => A.numberingLayout sel short
local notation "values" => A.numberingValues donorStart board xs next raw sel short shape
local notation "sensors" => A.originalSensorsAt donorStart first u N

include acquired jobs viewWidth afterMarkers space keys countWidth haloWidth kept in
/-- All three fields are read after the complete sparse publication and the previous
compact-inverse gather. The only signed data hypotheses concern the original sender. -/
theorem issued_original_columns {used denseH : ℕ} (rawName : Fin used→Fin A.sparseHosts)
    (at_ : Memory w) (preserved : ∀p,p<A.choicePage first→at_ p=A.held donorStart first u postTrunk p)
    (projectRoom : A.projected first<2^w) (base relayBase cutoff : ℕ)
    (count inverse : Bank) (ready : (panels).Ready base sensors w)
    (directory : (panels).Directory («H»:=denseH) rawName ((panels).after base sensors at_)
      relayBase count inverse cutoff) :
    let m:=(panels).after base sensors at_
    let relay:DescentResetDenseOperand.Layout:=⟨relayBase,denseH,A.sparseHosts,chunks A.groups M⟩
    (∀x s j,Source («H» := denseH) ((panels).label base relay count inverse x s j)
        ((panels).denseLabel («H» := denseH) rawName values x s j) M m) ∧
    (∀x s f j,Source («H» := denseH) ((panels).cargo base relay count inverse x s f j)
        ((panels).denseCargo («H» := denseH) rawName values x s f j) M m) :=by
  have prior:=A.numbered_reads donorStart first u board front markerEnd pack xs next raw initial postTrunk
    acquired jobs viewWidth afterMarkers space keys countWidth haloWidth kept projectRoom sel short shape at_ preserved
  have captured : (panels).Seen sensors values at_:=by
    rw [A.originalSensorsAt_full donorStart first u]
    exact prior
  exact (panels).dense_sources rawName values _ base relayBase count inverse cutoff directory
    ((panels).exhibits base sensors values at_ ready captured)

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI

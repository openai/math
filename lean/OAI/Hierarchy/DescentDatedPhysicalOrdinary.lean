import OAI.Hierarchy.DescentOrdinaryPaletteConfig
import OAI.Hierarchy.DescentOrdinaryMarkShapeRate
import OAI.Hierarchy.DescentDatedPriorHeader
import OAI.Hierarchy.DescentDatedMaterialExtent
import OAI.Hierarchy.DescentOrdinaryVenueExtent
import OAI.Hierarchy.DescentPrivateInstalledWidth
import OAI.Hierarchy.DescentDatedOriginPlan
import OAI.Hierarchy.DescentOrdinaryBornChart
import OAI.Hierarchy.DescentOrdinaryRefsShape
import OAI.Hierarchy.DescentDatedReturnMetadata
import OAI.Hierarchy.DescentDatedOrdinaryProfile
import OAI.Hierarchy.DescentOrdinaryFinalChart
import OAI.Hierarchy.DescentStageVenueChange
import OAI.Hierarchy.DescentDatedOrdinarySignedExtent
import OAI.Hierarchy.DescentDatedOrdinaryOutput
import OAI.Hierarchy.DescentDatedOrdinaryProgram
import OAI.Hierarchy.DescentDatedPriorOperandRate

namespace OAI
/-! # Original ordinary dates retain their actual normalization, operand roster and chosen receiver -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local DescentOperandVectorArena ProtocolRAM
noncomputable section
structure PhysicalOrdinary (F P : Type) [Field F] where
  dimension : ℕ
  bits : P→ℕ
  gadget : PoweredGadget F
  schedule : DescentCompiler.AtomSchedule
  q : ℝ
  u : ℝ
  ε : ℝ
  k : ℕ
  age : ℕ
  z : ℕ
  degree : ℕ
  wire : ℕ
  hist : ℕ
  nextZ : ℕ
  nextDegree : ℕ
  world : MarkedWorld F dimension P bits
  prior : Reached world gadget q ε schedule k age z degree wire hist
  nonnegative : 0≤ε
  stage : StageInput world gadget u ε
  choice : (stage.result nonnegative).Choice
  normalize : Normalize ((stage.result nonnegative).state choice)
  target : Reached normalize.result gadget q ε schedule k (age+1) nextZ nextDegree wire hist
  ticket : OrdinaryLink prior nonnegative stage choice normalize target
  old : Bank
  reference : DescentOrdinaryRefsROM.Chart
  bornBook : DescentOrdinaryBorn.Chart
  ingressWords : ℕ
  rasterLanes : ℕ
  vector : Layout
  resolver : DescentDatedPriorOperand.Layout
  origin : DescentDatedPriorOperand.OriginPlan resolver
  palette : DescentOrdinaryPalette.Configuration
  profileRepack : ProfileRepack
  metadata : MetadataReturn
  operandBook : DescentOrdinaryFinal.Chart
  signed : SignedExtent
  venue : DescentSixParty.StageVenueTail.Date
  level : ℕ
  bitsPerField : ℕ
  short : ℕ
  payload : ℕ
  unit : ℕ
  profile : ℕ
  seats : ℕ

namespace PhysicalOrdinary
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)
def area :=v.ticket.ordinaryArea v.level v.bitsPerField v.payload v.unit v.profile v.seats
def routeWords := v.origin.routeWords
def donorEnd (floor : ℕ) :=v.ticket.endAddress v.old floor v.level v.bitsPerField v.short v.payload v.unit v.profile v.seats
open DescentRawCablePanel DescentSIMDLookup
def material : MaterialExtent :=
  let fmt:=v.ticket.depotShape v.short
  ⟨v.area.H,v.area.G,lanes v.payload (v.ticket.installedDonorWidth v.short v.profile),
    v.signed.hosts,v.signed.groups,v.signed.lanes,fmt.blocks,v.signed.reach,fmt.cap,
    DepotRAM.totalBits fmt+DepotRAM.chartBits fmt,v.signed.fieldBits⟩
def materialStart (floor : ℕ) := PriorHeader.endAddress v.area.H v.signed.groups v.signed.lanes v.signed.degree (v.donorEnd floor)
def materialEnd (floor : ℕ) := v.material.endAddress (v.materialStart floor)
def peerTail (floor : ℕ) :=DescentOrdinaryVenueReturn.roof (v.materialEnd floor) v.area.H v.area.D v.venue.hosts v.venue.degree
def markShape : DescentOrdinaryMarkProject.Shape :=
  ⟨v.signed.reach,2^v.k,v.prior.placement.cap,v.prior.placement.degree,v.area.H,
    v.signed.hosts,v.signed.groups,v.signed.blocks,v.area.lanesAt,v.signed.lanes⟩
def markEnd (floor : ℕ) :=v.markShape.endAddress (v.peerTail floor)
def signedEnd (floor : ℕ) :=v.signed.roof (v.markEnd floor)
def reverseWords:=PriorHeader.endAddress v.area.H v.signed.groups v.signed.lanes v.signed.degree 0
def survivorWords :=v.reverseWords+v.material.endAddress 0+
    DescentOrdinaryVenueReturn.roof 0 v.area.H v.area.D v.venue.hosts v.venue.degree+v.markShape.endAddress 0+v.signed.roof 0

theorem donor_shift (floor : ℕ) : v.donorEnd floor=floor+v.donorEnd 0 :=
  v.ticket.end_relocate v.old floor v.level v.bitsPerField v.short v.payload v.unit v.profile v.seats

theorem signed_extent (floor : ℕ) : v.signedEnd floor=v.donorEnd floor+v.survivorWords:=by
  rw [signedEnd,v.signed.shift,markEnd,v.markShape.translated,peerTail,DescentOrdinaryVenueReturn.shift,materialEnd,v.material.translated,materialStart,PriorHeader.translated]
  simp only [survivorWords,reverseWords,Nat.add_assoc]

theorem signed_stage_paid (floor : ℕ) :
    v.donorEnd floor≤v.materialEnd floor ∧ v.materialEnd floor≤v.peerTail floor ∧ v.peerTail floor≤v.signedEnd floor:=by
  refine ⟨?_,?_,(v.markShape.low _).trans (v.signed.room _)⟩
  · rw [materialEnd,v.material.translated]
    exact (PriorHeader.lower _ _ _ _ _).trans <| Nat.le_add_right ..
  · rw [peerTail,DescentOrdinaryVenueReturn.shift]
    exact Nat.le_add_right ..
def refsStart (floor : ℕ) :=v.signedEnd floor+v.ingressWords
def birthStart (floor : ℕ) :=v.refsStart floor+v.reference.extent
def vectorStart (floor : ℕ) :=v.bornBook.endAddress (v.birthStart floor)
def routedStart (floor : ℕ) :=v.vector.endAddress (v.vectorStart floor)
def normalizedEnd (floor : ℕ) :=v.routedStart floor+v.routeWords
def referenceWords := ((v.ingressWords+v.reference.extent)+v.bornBook.endAddress 0)+v.routeWords
def argumentExtra := v.survivorWords+v.referenceWords

theorem routed_le (floor : ℕ) : v.routedStart floor≤v.normalizedEnd floor:=Nat.le_add_right ..
theorem vector_before (floor : ℕ) : v.vectorStart floor≤v.routedStart floor:=by
  change _≤v.vector.endAddress _
  rw [DescentOperandVectorArena.affine]
  exact Nat.le_add_right ..

theorem arguments_extent (floor : ℕ) : v.normalizedEnd floor=
    v.ticket.outputEnd v.old v.vector floor v.level v.bitsPerField v.short v.payload v.unit v.profile v.seats+v.argumentExtra :=by
  change v.vector.endAddress (v.bornBook.endAddress (v.birthStart floor))+v.routeWords=
    v.vector.endAddress (v.donorEnd floor)+v.argumentExtra
  rw [DescentOperandVectorArena.affine v.vector (v.bornBook.endAddress _),DescentOperandVectorArena.affine v.vector (v.donorEnd floor),v.bornBook.affine (v.birthStart floor)]
  simp only [birthStart,refsStart,argumentExtra,referenceWords,v.signed_extent]
  omega
/-- Literal census, local choice, topology, birth and selected-rotation code at the
same floor subsequently passed through the donor workspace into the argument vector. -/
def rotationProgram (input : Stage.Dated.Operands) (w floor : ℕ) :=
  v.area.program v.gadget v.prior.placement.fieldBits input
    ⟨v.prior.placement.wire,v.prior.placement.z,v.prior.placement.hist⟩ w floor

def endAddress (base : ℕ) :=v.resolver.endAddress (v.normalizedEnd base)
def ceiling :=v.area.ordinaryWords v.old v.vector+v.argumentExtra+v.resolver.endAddress 0
theorem spent (base : ℕ) : base≤v.endAddress base ∧ v.endAddress base≤base+v.ceiling ∧
    v.endAddress base=base+v.endAddress 0 := by
  have prev:=v.ticket.output_coordinates v.old v.vector base v.level v.bitsPerField v.short v.payload v.unit v.profile v.seats
  have addBase:=v.arguments_extent base
  have addZero:=v.arguments_extent 0
  have endBase:=v.resolver.affine (v.normalizedEnd base)
  have endZero:=v.resolver.affine (v.normalizedEnd 0)
  change base≤v.endAddress base ∧ v.endAddress base≤base+(v.area.ordinaryWords v.old v.vector+v.argumentExtra+v.resolver.endAddress 0) ∧ _
  change v.endAddress base=v.normalizedEnd base+v.resolver.endAddress 0 at endBase
  change v.endAddress 0=v.normalizedEnd 0+v.resolver.endAddress 0 at endZero
  obtain ⟨one,two,three⟩:=prev
  change _≤base+v.area.ordinaryWords v.old v.vector at two
  omega
theorem rate {ι : ℕ→Type*} {Pins : ∀h,ι h→Type} (v : ∀h (i:ι h),PhysicalOrdinary F (Pins h i))
    (b : Stage.Dated.Ordinary.ScalarRoom (fun h i=>(v h i).area))
    (six : ∀h i,DescentPacking.PackedMatch.SixBirths.unit (v h i).area.shapeAt≤(v h i).unit)
    (vector : Layout.ScalarRoom (fun h i=>(v h i).vector))
    (reverse : Bounded (fun h i=>(v h i).reverseWords))
    (material : MaterialExtent.ScalarRoom (fun h i=>(v h i).material))
    (peers : Bounded (fun h i=>DescentOrdinaryVenueReturn.roof 0 (v h i).area.H (v h i).area.D
      (v h i).venue.hosts (v h i).venue.degree))
    (marks : DescentOrdinaryMarkProject.Shape.ScalarRoom (fun h i=>(v h i).markShape))
    (signed : SignedExtent.ScalarRoom (fun h i=>(v h i).signed))
    (extra : Bounded (fun h i=>(v h i).referenceWords))
    (resolved : DescentDatedPriorOperand.Layout.ScalarRoom (fun h i=>(v h i).resolver)) :
    Bounded (fun h i=>(v h i).ceiling) :=
  ((Stage.Dated.Ordinary.ordinary_words_rate _ _ _ b six vector).add (
    (((((reverse.add (MaterialExtent.extent_rate _ material)).add peers).add (DescentOrdinaryMarkProject.Shape.extent_rate _ marks))).add (SignedExtent.rate _ signed)).add extra)).add (DescentDatedPriorOperand.Layout.extent_rate _ resolved)

end PhysicalOrdinary
end
end Hierarchy.DescentSixParty.Chronology

end OAI

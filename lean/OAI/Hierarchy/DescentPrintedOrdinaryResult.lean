import OAI.Hierarchy.DescentOrdinaryProgramBlocks
import OAI.Hierarchy.DescentOrdinaryFundedProgram
import OAI.Hierarchy.DescentDatedPrimitiveCode
import OAI.Hierarchy.DescentOrdinaryArgumentPhaseUnique
import OAI.Hierarchy.DescentSignedPublicPrefix
import OAI.Hierarchy.DescentOrdinaryResultSteps

namespace OAI
/-! # Numeric representation of all six consecutive parts of a real ordinary successor -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup DescentDatedAddressBook
open DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (root : ℕ) (input : Dated.Operands)
  (count : Bank) (A : ArgumentEntry v) (c : v.SignedChart) {w : ℕ}
local notation "floor" => v.stageStart root
variable (matched : A.Match v (v.stageStart root)) (paths : A.clip.venue.paths=StageVenueTail.OrdinaryRaster.paths v.area)
    (src : OriginSources v) (prepare : NativePhase w)
local notation "fund" => v.fundedFromEntry floor A paths
local notation "roster" => (⟨count,input.roster,input.hubs⟩:DescentOrdinaryVenueReturn.Sources)

def resultCode (B : StageVenueTail.Sources) : OrdinaryResultCode w :=
  let code:=(v.argumentPlan floor A matched src).emit (ArgumentPlan.view prepare)
  let four:=(v.signedProgram floor).four (v.publicSignedChart floor c) w A.venue.panel A.venue.adjacency roster input
  let top:=(v.area.matcher v.old floor).layout.topology
  let f:=DescentPacking.PackedMatch.chunkCount v.area.shapeAt v.area.lanesAt
  ⟨.ofPhase four,⟨code.program,code.ticks⟩,
    FundedProgram.fromChart v.returnChart (v.donorEnd floor) (fund).field (fund).ports input w,
    v.returnProgram floor B,.ofPhase ((v.primitiveDevice floor A).phase w),
    ⟨DescentOrdinaryCountScan.program w top f (v.primitiveEnd floor) v.area.batch,
     DescentOrdinaryCountScan.clock v.countBits v.area.batch⟩⟩

theorem result_printed (B : StageVenueTail.Sources) (chip : (A.chipBank v floor).Fits w (v.refsStart floor))
    (shape : v.VectorShape) (fit : v.endAddress floor<2^w)
    (packed : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (radix : v.vector.radix=2^v.reference.k) (ok : v.FundedRoom floor fund input w) :
    let steps:=v.ordinaryResultSteps floor input A matched paths src prepare chip shape fit packed radix ok
    v.printedResult root input count (v.signedInput floor c) B steps=
      v.resultCode root input count A c matched paths src prepare B :=by
  intro steps
  have args:=v.argumentPlan_emit floor A matched src prepare chip shape fit packed
  have prim:=v.primitive_device floor A matched radix w
  have funds:=v.funded_calendar floor fund input ok
  dsimp only [printedResult,steps,ordinaryResultSteps,resultCode]
  rw [args,prim,funds]
  rfl

theorem date_result_code (B : StageVenueTail.Sources) (chip : (A.chipBank v floor).Fits w (v.refsStart floor))
    (shape : v.VectorShape) (fit : v.endAddress floor<2^w)
    (packed : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (radix : v.vector.radix=2^v.reference.k) (ok : v.FundedRoom floor fund input w)
    (shelf header : ℕ) (room : v.ResultRoom floor B w) (d : DonorDate) (positive : 0<d.exponent) :
    let steps:=v.ordinaryResultSteps floor input A matched paths src prepare chip shape fit packed radix ok
    let result : PrintedStep w := (v.resultCode root input count A c matched paths src prepare B).printed
    let load:=v.archivePhase root shelf w
    v.date root shelf header input count (v.signedInput floor c) B steps room d positive=
      d.codeLoadedAfter v.gadget positive v.payload v.seats v.bitsPerField floor header w input
        ⟨v.prior.placement.wire,v.prior.placement.z,v.prior.placement.hist⟩
        load.program load.ticks result.program result.ticks :=by
  intro steps result load
  have same:=v.result_printed root input count A c matched paths src prepare B chip shape fit packed radix ok
  have issue:=v.date_printed root shelf header input count (v.signedInput floor c) B steps room d positive
  simpa only [steps,same] using issue

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

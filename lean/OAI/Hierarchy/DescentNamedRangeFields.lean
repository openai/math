import OAI.Hierarchy.DescentNamedBankRangeAmount
import OAI.Hierarchy.DescentPostedRelaySpans
import OAI.Hierarchy.DescentPostedUnoccupiedSpans
import OAI.Hierarchy.DescentOccupiedResetRoleCases
import OAI.Hierarchy.DescentRegisteredBankEmpty
import OAI.Hierarchy.DescentPublicRowsOfOrigins

namespace OAI
/-! # Physical range fields across an original reset date -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
open DescentBundleHistory DescentPacking.PackedMatch.Local.Stage DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F X : Type} [Field F] {d : ℕ} {abits : X→ℕ} {W : MarkedWorld F d X abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
local notation "E" => (a).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)

open DescentSortedRoster
local notation "imageOf" degreeAt capAt => fromNamed_root_image (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "prior_" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation "C₀" => (v).setup
open DescentLocalArchiveOrder DescentKernelHistory DescentBundleHistory DescentPrimitivePalette
open DescentGL DescentFallbackPeriod.Projected DescentCommonHost
open DescentDatedPriorOperand DescentRetainedRangeDigits DescentLocalPrivateNames
open DescentResetOperandSetup DescentPacking.PackedMatch.Local.Stage
open DescentSixParty.Chronology DescentSixParty.ClosedReset DescentSixParty.ClosedReset.Window
open scoped BigOperators
local notation "K" => (C₀).retained
local notation "Rports" => DatePorts.reset a start u
local notation "panels" => DateInputs.OperandPanelsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
local notation "menus" => DateInputs.PublicOperandRowsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
variable [Fintype X] {R:ℕ} (oldA:Archive W) (oldNum:Local oldA.bit) (shape:WorldShape p R oldA.bit)
    (hp:0<p) (one:1≤R) (unitPos:0<(Z).unit) (whole:p∣(Z).unit)
    (widthBound:max 1 (max (Z).width (C*(Z).width))≤R) (pin:X→ℕ)
local notation "after_" => (resetArchive B p hp whole oldA).bit
local notation "order_" => DescentLocalArchiveOrder.reset B p hp whole oldA oldNum
local notation "shape₁" => reset_shape_at hp one B oldA shape unitPos whole widthBound
variable (ready:(u).Ready) (actorMem:Memory w) (small:2*(v).receiver.candidates<2^(v).receiver.queryBits)
    (axes:(Rports).rangeLayout=(v).rangeLayout) (choices:∀i,DatePorts.OrdinalRead (u) ready small actorMem i)
    (places:DatePorts.RangeRoom Rports B.next after_)
    (previousCapacity:∀v₀,Fintype.card (oldA.bit.recipe v₀).Node≤(K).previousNodes)
    (previousArgs:∀v₀ n₀,((shape.sites v₀).recipe hp).arity n₀≤(K).previousArgs)
    (arity:∀v₀ n₀,(((shape₁).sites v₀).recipe hp).arity n₀≤(Rports).argumentsPerNode)
variable (degreeAt:venue.degree=D) (capAt:input.placement.cap=cap)
    (height:0<S.height) (base:G.b≤2^S.capGain) (grainAt:z=S.grainAt G.b p (age+1))
    (oldValues:(K).Values) (μ:DescentGL.Layout (E).dim) (measured:Memory w)
    (won:HEq μ B.frame.basis)
    (public_:menus ready actorMem)
local notation "geom_" => S.previousGeometry G k tail drift degree p age payload (prior_).nodes
    (prior_).arguments (prior_).operandLanes ctl.base ctl.radix B.age
local notation "total_" => (geom_).1
local notation "axis_" => (B.commonDepth.symm:(K).cut=(T).commonDepth)
local notation "hostRoom" => (input.valid.host:Fintype.card input.V≤(K).hosts)
variable (previousRows:∀(G₀:(C₀).MovementShape) (basis:DescentGL.Layout ((K).high+(K).low)),
    HEq basis B.frame.basis→Window.PrimaryDonorRead B (C₀) oldA oldNum shape hp pin total_ axis_ rfl rfl
      G₀.size G₀.cut hostRoom previousCapacity previousArgs basis oldValues)

local notation "ranges_" => DateInputs.RangeRequestsAt (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom degreeAt capAt ready oldValues μ measured actorMem
variable (rangeRows:ranges_)
variable (inputMem:Memory w)
local notation "originalAt" => DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom degreeAt ready inputMem capAt μ measured actorMem
variable (original:originalAt) (elapsed:0<age) (sorted:SourceSorted W input.order)
    (earnedWidth:max 1 (max (Z).width (C*(Z).width))≤drift)
    (counts:∀(geo:(C₀).MovementShape) (basis:DescentGL.Layout ((K).high+(K).low)),
      OriginalRootCounts (input:=input) (oldA:=oldA) (K) oldValues geo.size geo.cut basis hostRoom rfl rfl)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
include accepted previousRows rangeRows original elapsed sorted earnedWidth counts base grainAt in
/-- The one named reset receiver returns the original three range fields at every
occupied slot and zero argument count at every remaining position of the same output. -/
theorem DateInputs.named_range_fields :
    DatePorts.SevenSpans (u) B.next after_ order_ places shape₁ ready small axes actorMem choices ∧
    DatePorts.SevenVacant (u) B.next after_ order_ places ready small axes actorMem choices :=by
  have publicRows:=DateInputs.public_rows_of_origins (B:=B) drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom degreeAt ready inputMem capAt original
  have chosen:HEq μ B.frame.basis:=original.1
  have copied:=rangeRows
  obtain ⟨_,_,_,_,_,_,dirSize,_⟩:=copied
  have zeroCounts (geo:(C₀).MovementShape) (basis:DescentGL.Layout ((K).high+(K).low))
      (_:HEq basis B.frame.basis):=counts geo basis
  constructor
  · apply DatePorts.registered_seven_spans (u) B.next after_ order_ places shape₁ ready small axes actorMem choices
      (resetOrigin B hp whole oldA)
    · exact DateInputs.registered_retained_spans (B:=B) (oldA:=oldA) (oldNum:=oldNum)
        (shape:=shape) (hp:=hp) (one:=one) (unitPos:=unitPos) (whole:=whole) (widthBound:=widthBound)
        (pin:=pin) (ready:=ready) (actorMem:=actorMem) (small:=small) (axes:=axes) (choices:=choices)
        (places:=places) (previousCapacity:=previousCapacity) (previousArgs:=previousArgs) (μ:=μ)
        (measured:=measured) (won:=chosen) (degreeAt:=degreeAt) (capAt:=capAt) (public_:=publicRows)
        (previousRows:=previousRows) (rangeRows:=rangeRows)
    · exact DateInputs.registered_relay_spans (B:=B) (accepted:=accepted) (rangeRows:=rangeRows)
        (origins:=original) (choices:=choices) (places:=places) (grainAt:=grainAt) (shape:=shape)
        (one:=one) (unitPos:=unitPos) (widthBound:=widthBound) elapsed sorted
    · exact DateInputs.registered_bank_spans (B:=B) (accepted:=accepted) (archive:=oldA) (earlier:=oldNum)
        (shape:=shape) (one:=one) (positive:=unitPos) (widthBound:=widthBound) (wordBound:=earnedWidth)
        (ready:=ready) (small:=small) (axes:=axes) (choices:=choices) (places:=places) (requests:=rangeRows)
        (m:=inputMem) (gr:=grainAt) (original:=original) (base:=base) (elapsed:=elapsed) (sorted:=sorted)
  · apply DatePorts.registered_seven_vacant (u) B.next after_ order_ places ready small axes actorMem choices
    · intro xb j hh gg nn outside _
      exact DateInputs.registered_exterior_span (B:=B) drift degree payload e previous M nextM oldLanes
        primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
        initial prepared sceneRoom ready actorMem small axes choices degreeAt capAt oldValues μ measured
        rangeRows inputMem original xb j hh gg nn outside 2
    · intro xb j hh gg nn actual emptySite absent
      exact DateInputs.registered_unoccupied_span (B:=B) drift degree payload e previous M nextM oldLanes
        primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
        initial prepared sceneRoom oldA oldNum hp whole ready actorMem small axes choices places
        degreeAt capAt oldValues μ measured chosen rangeRows inputMem original zeroCounts xb j hh gg nn actual emptySite absent 2
    · intro xb j hh gg nn actual site used _ absent
      have cases_:=DateInputs.occupied_role_cases (B:=B) drift degree payload e previous M nextM oldLanes
        primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
        initial prepared sceneRoom degreeAt oldA hp whole Rports places xb hh gg actual dirSize site used
      rcases cases_ with retained|⟨relay,atRelay⟩|⟨bank,atBank⟩
      · exact DateInputs.registered_primary_vacant (B:=B) drift degree payload e previous M nextM oldLanes
          primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
          initial prepared sceneRoom oldA oldNum hp whole ready actorMem small axes choices places
            degreeAt capAt oldValues μ measured chosen rangeRows inputMem original zeroCounts dirSize xb j hh gg nn actual absent retained 2
      · subst site
        exact DateInputs.registered_relay_empty (B:=B) (axes:=axes) (accepted:=accepted) (rangeRows:=rangeRows)
          (origins:=original) (choices:=choices) (places:=places) (grainAt:=grainAt)
          xb j hh gg nn actual relay used absent 2
      · subst site
        exact DateInputs.registered_bank_empty (B:=B) accepted drift degree payload e previous M nextM oldLanes
          primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
          initial prepared sceneRoom hp whole oldA oldNum degreeAt capAt grainAt base elapsed sorted ready inputMem
          oldValues μ measured actorMem original rangeRows small axes choices places xb j hh gg nn actual bank used absent

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI

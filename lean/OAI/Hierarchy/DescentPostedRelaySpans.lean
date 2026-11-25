import OAI.Hierarchy.DescentNamedRangePanelRelay
import OAI.Hierarchy.DescentNamedOperandWordRoom
import OAI.Hierarchy.DescentRegisteredSevenSpans
import OAI.Hierarchy.DescentIssuedResetShape

namespace OAI
/-! The three relay range digits at their physical register coordinates. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
open DescentPacking.PackedMatch.Local.Stage DescentSixParty.Chronology
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
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "E" => (a).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
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

open DescentSortedRoster
local notation "C₀" => (v).setup
open DescentLocalArchiveOrder DescentKernelHistory DescentBundleHistory DescentPrimitivePalette
open DescentGL DescentFallbackPeriod.Projected DescentCommonHost
open DescentDatedPriorOperand DescentRetainedRangeDigits DescentLocalPrivateNames
open DescentResetOperandSetup DescentPacking.PackedMatch.Local.Stage
open DescentSixParty.Chronology DescentSixParty.ClosedReset DescentSixParty.ClosedReset.Window
open scoped BigOperators
local notation "K" => (C₀).retained
local notation "Rports" => DatePorts.reset a start u
variable [Fintype X] {R:ℕ} (oldA:Archive W) (oldNum:Local oldA.bit) (shape:WorldShape p R oldA.bit)
    (hp:0<p) (one:1≤R) (unitPos:0<(Z).unit) (whole:p∣(Z).unit)
    (widthBound:max 1 (max (Z).width (C*(Z).width))≤R)
local notation "after_" => (resetArchive B p hp whole oldA).bit
local notation "order_" => DescentLocalArchiveOrder.reset B p hp whole oldA oldNum
local notation "shape₁" => reset_shape_at hp one B oldA shape unitPos whole widthBound
variable (ready:(u).Ready) (actorMem:Memory w) (small:2*(v).receiver.candidates<2^(v).receiver.queryBits)
    (axes:(Rports).rangeLayout=(v).rangeLayout) (choices:∀i,DatePorts.OrdinalRead (u) ready small actorMem i)
    (places:DatePorts.RangeRoom Rports B.next after_)
variable (degreeAt:venue.degree=D) (capAt:input.placement.cap=cap)
    (grainAt:z=S.grainAt G.b p (age+1))
    (oldValues:(K).Values) (μ:DescentGL.Layout (E).dim) (measured:Memory w)
local notation "ranges_" => DateInputs.RangeRequestsAt (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom degreeAt capAt ready oldValues μ measured actorMem
variable (rangeRows:ranges_)

variable (inputMem : Memory w)
local notation "origins_" => DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
  previousArguments initial prepared sceneRoom degreeAt ready inputMem capAt μ measured actorMem
variable (origins : origins_)

local notation "spanLayout" => (Rports).rangeLayout
local notation:max "xx" x:arg => (x:Fin (spanLayout).blocks).cast (congrArg DescentDatedPriorOperand.Layout.blocks axes)
local notation:max "jj" j:arg => ((j:Fin (spanLayout).operands).cast (congrArg DescentDatedPriorOperand.Layout.operands axes)).cast ready.slots.symm
local notation:max "nn" n:arg => ((n:Fin (spanLayout).nodes).cast (congrArg DescentDatedPriorOperand.Layout.nodes axes)).cast ready.nodes.symm
local notation:max "hh" h:arg => (h:Fin (spanLayout).hosts).cast (congrArg DescentDatedPriorOperand.Layout.hosts axes)
local notation:max "gg" g:arg => (g:Fin (spanLayout).groups).cast (congrArg DescentDatedPriorOperand.Layout.groups axes)
local notation:max "digit" f:arg j:arg x:arg n:arg h:arg g:arg => ((choices ((v).operandOrdinal (u).operand (page f)
  (jj j) (xx x) (nn n))).amount (hh h) (gg g)).val
local notation "hit" => DatePorts.slotAt Rports B.next after_ order_ places
local notation "amountRoom" => DateInputs.named_amount_rooms G S board k tail age p f g drift degree payload e previous M nextM
  C packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
  previousArguments initial prepared sceneRoom ready

variable {accepted drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w
  fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
  oldA oldNum shape hp one unitPos whole widthBound ready actorMem small axes choices places degreeAt capAt grainAt
  oldValues μ measured rangeRows inputMem origins}

set_option maxRecDepth 4096 in
set_option maxHeartbeats 900000 in
include accepted grainAt origins rangeRows in
omit [Fintype X] in
theorem DateInputs.registered_relay_spans (elapsed : 0<age) (sorted : SourceSorted W input.order) :
    DatePorts.SevenOriginSpans (u) B.next after_ order_ places shape₁ ready small axes actorMem choices
      (resetOrigin B hp whole oldA) (Sum.inr ∘ Sum.inl) := by
  intro x j axis h group n y slot _ edge origin
  have registers := rangeRows
  obtain ⟨_,_,_,_,_,_,size_,_⟩ := registers
  have packed := amountRoom
  exact DateInputs.range_panel_relay (B:=B) accepted drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom (oldA:=oldA) (num:=oldNum) (hp:=hp)
    (whole:=whole) (ports:=Rports) (places:=places) (block:=x) (node:=n) (rack:=h) (group:=group)
    (one:=one) (posUnit:=unitPos) (widthBound:=widthBound) (shape:=shape)
    (degreeAt:=degreeAt) (capAt:=capAt) (grainAt:=grainAt) (ready:=ready)
    (archived:=oldValues) (μ:=μ) (m:=inputMem) (measured:=measured) (actors:=actorMem)
    (requests:=rangeRows) (original:=origins) (size:=size_)
    (x₀:=xx x) (arg:=jj j) (newNode:=nn n) (rh:=hh h) (rg:=gg group)
    (blockAt:=rfl) (nodeAt:=rfl) (hostAt:=rfl) (groupAt:=rfl)
    (small:=small) (choice:=fun i=>choices ((v).operandOrdinal (u).operand i (jj j) (xx x) (nn n)))
    (live:=ready.placed.lanes) (bus:=packed.2.1) (lane:=packed.2.2) y edge slot origin elapsed sorted axis

set_option maxRecDepth 4096 in
set_option maxHeartbeats 900000 in
include accepted grainAt origins rangeRows in
omit [Fintype X] in
theorem DateInputs.registered_relay_empty
    (x : Fin (spanLayout).blocks) (j : Fin (spanLayout).operands) (h : Fin (spanLayout).hosts)
    (group : Fin (spanLayout).groups) (n : Fin (spanLayout).nodes) (present : h.val<Fintype.card B.next.V)
    (t : (Z).Fallback)
    (here : DescentPaidResidentCount.occupies B.next.placement (Equiv.refl _) B.next.vertex ⟨h.val,present⟩
      (group.cast places.groups.symm) (x.cast (congrArg (2^·) places.radix.symm))
      (B.reblock.destination (((Z).resetNames T).symm (.inl (true,t)))))
    (absent : hit x n h group=none) (axis : Fin 3) : digit axis j x n h group=0 := by
  have registers := rangeRows
  obtain ⟨_,_,_,_,_,_,size_,_⟩ := registers
  have packed := amountRoom
  exact DateInputs.range_panel_relay_vacant (B:=B) accepted drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom (oldA:=oldA) (num:=oldNum)
    (hp:=hp) (whole:=whole) (ports:=Rports) (places:=places) (block:=x) (node:=n) (rack:=h)
    (group:=group) (degreeAt:=degreeAt) (capAt:=capAt) (grainAt:=grainAt) (ready:=ready)
    (archived:=oldValues) (μ:=μ) (m:=inputMem) (measured:=measured) (actors:=actorMem)
    (requests:=rangeRows) (original:=origins) (size:=size_)
    (x₀:=xx x) (arg:=jj j) (newNode:=nn n) (rh:=hh h) (rg:=gg group)
    (blockAt:=rfl) (nodeAt:=rfl) (hostAt:=rfl) (groupAt:=rfl)
    (small:=small) (choice:=fun i=>choices ((v).operandOrdinal (u).operand i (jj j) (xx x) (nn n)))
    (live:=ready.placed.lanes) (bus:=packed.2.1) (lane:=packed.2.2) t present here absent axis

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI

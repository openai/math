import OAI.Hierarchy.DescentNamedPanelPublicCapacity
import OAI.Hierarchy.DescentRegisteredRetainedSlot
import OAI.Hierarchy.DescentNamedOperandWordRoom
import OAI.Hierarchy.DescentIssuedResetShape
import OAI.Hierarchy.DescentNamedRangePanelPrimary
import OAI.Hierarchy.DescentRegisteredSevenSpans

namespace OAI
/-! The three range fields at every reached, retained register position. -/
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
local notation "namedReset" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "namedSuccessor" => (namedReset).successor
local notation "start" => (namedReset).stageStart floor
local notation "base₀" => (namedReset).rebased start
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
local notation "rc" => (namedReset).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (namedReset).stencilPhase sh start count io.hubs g (2^n)
local notation "E" => (namedReset).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (namedSuccessor).middle.stop base₀
local notation "early" => (namedSuccessor).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (namedSuccessor).front.SceneRoom early ((namedSuccessor).issuedScene base₀ older) w)
local notation "dateInput" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "entry₀" => (namedReset).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)

open DescentSortedRoster
local notation "imageOf" degreeAt:arg capAt:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "prior_" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation "C₀" => (namedSuccessor).setup
open DescentLocalArchiveOrder DescentKernelHistory DescentBundleHistory DescentPrimitivePalette
open DescentGL DescentFallbackPeriod.Projected DescentCommonHost
open DescentDatedPriorOperand DescentRetainedRangeDigits DescentLocalPrivateNames
open DescentResetOperandSetup DescentPacking.PackedMatch.Local.Stage DescentRetainedPrivateSlotBook
open DescentRetainedResetPinPointer DescentSixParty.Chronology DescentSixParty.ClosedReset DescentSixParty.ClosedReset.Window
open scoped BigOperators
local notation "K" => (C₀).retained
local notation "Rports" => DatePorts.reset namedReset start dateInput
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
variable (ready:(dateInput).Ready) (actorMem:Memory w) (small:2*(namedSuccessor).receiver.candidates<2^(namedSuccessor).receiver.queryBits)
    (axes:(Rports).rangeLayout=(namedSuccessor).rangeLayout) (choices:∀i,DatePorts.OrdinalRead (dateInput) ready small actorMem i)
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
set_option maxRecDepth 4096 in
set_option maxHeartbeats 850000 in
omit [Fintype X] in
include previousRows won public_ rangeRows in
theorem DateInputs.registered_retained_spans :
    DatePorts.SevenOriginSpans (dateInput) B.next after_ order_ places shape₁ ready small axes actorMem choices
      (resetOrigin B hp whole oldA) Sum.inl:=by
  have registers:=rangeRows
  obtain ⟨_,_,_,_,_,_,size_,_⟩:=registers
  have packed:=DateInputs.named_amount_rooms G S board k tail age p f g drift degree payload e previous M nextM
    C packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom ready
  have ret:=DatePorts.registered_retained_capacity (dateInput) ready axes
  have bitRoom:(K).bits≤(C₀).fieldBits:=Nat.le_max_left ..
  have width:(K).bits≤(namedSuccessor).receiver.valueBits:=le_rfl
  intro xb j f₀ h₀ g₀ n₀ y slot admissible old origin
  let x:=xb.cast (congrArg DescentDatedPriorOperand.Layout.blocks axes)
  let arg:Fin (K).args:=(j.cast (congrArg DescentDatedPriorOperand.Layout.operands axes)).cast ready.slots.symm
  let node:Fin (K).nodes:=(n₀.cast (congrArg DescentDatedPriorOperand.Layout.nodes axes)).cast ready.nodes.symm
  let hostIndex:=h₀.cast (congrArg DescentDatedPriorOperand.Layout.hosts axes)
  let groupIndex:=g₀.cast (congrArg DescentDatedPriorOperand.Layout.groups axes)
  obtain ⟨values,valid,_⟩:=public_ size_ x
  have reported:=DateInputs.range_panel_primary (F:=F) (Pin:=X) (d:=d) (abits:=abits) (W:=W)
    (G:=G) (q:=q) (ε:=ε) (S:=S) (k:=k) (age:=age) (z:=z) (wire:=wire) (hist:=hist)
    (D:=D) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (cut:=cut) (tail:=tail) (p:=p)
    (input:=input) (ctl:=ctl) (B:=B) (R:=R)
    (drift:=drift) (degree:=degree) (payload:=payload) (e:=e) (previous:=previous) (M:=M)
    (nextM:=nextM) (oldLanes:=oldLanes) (primitiveLanes:=primitiveLanes) (printedBits:=printedBits)
    (venue:=venue) (io:=io) (floor:=floor) (w:=w) (fitsStencil:=fitsStencil) (fitsSigned:=fitsSigned)
    (fitsCut:=fitsCut) (count:=count) (previousMeta:=previousMeta) (previousArguments:=previousArguments)
    (initial:=initial) (prepared:=prepared) (sceneRoom:=sceneRoom) (degreeAt:=degreeAt) (capAt:=capAt)
    (oldA:=oldA) (num:=oldNum) (hp:=hp) (one:=one)
    (whole:=whole) (posUnit:=unitPos) (widthBound:=widthBound) (shape:=shape) (pin:=pin)
    (ports:=Rports) (places:=places) (block:=xb) (node:=n₀) (rack:=h₀) (group:=g₀) (now:=y) (old:=old)
    (slotAt:=slot) (source:=origin) (size:=size_) (ready:=ready) (archived:=oldValues) (μ:=μ)
    (measured:=measured) (actors:=actorMem) (requests:=rangeRows) (won:=won) (total:=total_) (oldBlocks:=rfl)
    (oldGroups:=rfl) (oldRoom:=previousCapacity) (oldArgs:=previousArgs) (newRoom:=(places.capacity y.1).trans_eq ret.2)
    (original:=fun shape dim=>previousRows shape (cast (congrArg DescentGL.Layout dim) μ) ((cast_heq _ μ).trans won))
    (x₀:=x) (arg:=arg) (newNode:=node) (rh:=hostIndex) (rg:=groupIndex) (blockAt:=rfl) (nodeAt:=rfl)
    (hostAt:=rfl) (groupAt:=rfl) (fieldRoom:=bitRoom) (outRoom:=width) (values:=values) (published:=valid)
    (small:=small) (choice:=fun axis=>choices ((namedSuccessor).operandOrdinal (dateInput).operand axis arg x node))
    (live:=ready.placed.lanes) (bus:=packed.2.1) (lane:=packed.2.2) f₀
  exact reported

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI

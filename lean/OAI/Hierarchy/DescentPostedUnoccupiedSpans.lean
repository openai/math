import OAI.Hierarchy.DescentPostedRetainedSpans
import OAI.Hierarchy.DescentNamedRangePanelInactive
import OAI.Hierarchy.DescentNamedRangePanelPrimaryEmpty
import OAI.Hierarchy.DescentPublicRowsOfOrigins

namespace OAI
/-! # The original range writer on empty host and node coordinates -/

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
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D boardOrder boardDegree C f reservedGain cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D boardOrder boardDegree C f reservedGain cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "namedReset" => named G S board k tail age p f reservedGain drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "namedSuccessor" => (namedReset).successor
local notation "start" => (namedReset).stageStart floor
local notation "base₀" => (namedReset).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds reservedGain S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree boardOrder f reservedGain
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f reservedGain drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f reservedGain drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f reservedGain drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (namedReset).rootPhase sh start count io.hubs reservedGain (2^boardOrder) roots w
local notation "P" => (namedReset).stencilPhase sh start count io.hubs reservedGain (2^boardOrder)
local notation "E" => (namedReset).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs reservedGain (2^boardOrder) roots w
local notation "actorBase" => (namedSuccessor).middle.stop base₀
local notation "early" => (namedSuccessor).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f reservedGain drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f reservedGain drift degree payload e previous M nextM C packet
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
local notation "ranges_" => DateInputs.RangeRequestsAt (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom degreeAt capAt ready oldValues μ measured actorMem
variable (rangeRows:ranges_)

variable (inputMem : Memory w)
local notation "origins_" => DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
  previousArguments initial prepared sceneRoom degreeAt ready inputMem capAt μ measured actorMem
variable (origins : origins_)
    (census : ∀ (geo:(C₀).MovementShape) (basis:DescentGL.Layout ((K).high+(K).low)),
      HEq basis B.frame.basis → OriginalRootCounts (input:=input) (oldA:=oldA) (K) oldValues
        geo.size geo.cut basis hostRoom rfl rfl)
local notation "spanLayout" => (Rports).rangeLayout
local notation "directorySize" => S.hostSize age*
  (DescentDenseHostOrder.roster (Z).graph ((Z).k-(T).commonDepth) (GroupStage.depthBound D boardOrder f reservedGain)).card=(C₀).placement.sparse
local notation "denseAt" size:arg r:arg => ((Z).rawAtIndex (T)
  (B.frame.host.symm.toEmbedding.trans (input.vertex.trans (Fin.castLEEmb input.valid.host))) r).cast size
local notation "xx" x:arg => (x:Fin (spanLayout).blocks).cast (congrArg DescentDatedPriorOperand.Layout.blocks axes)
local notation "jj" j:arg => ((j:Fin (spanLayout).operands).cast (congrArg DescentDatedPriorOperand.Layout.operands axes)).cast ready.slots.symm
local notation "nn" boardOrder:arg => ((boardOrder:Fin (spanLayout).nodes).cast (congrArg DescentDatedPriorOperand.Layout.nodes axes)).cast ready.nodes.symm
local notation "hh" boardDegree:arg => (boardDegree:Fin (spanLayout).hosts).cast (congrArg DescentDatedPriorOperand.Layout.hosts axes)
local notation "gg" reservedGain:arg => (reservedGain:Fin (spanLayout).groups).cast (congrArg DescentDatedPriorOperand.Layout.groups axes)
local notation "digit" f:arg j:arg x:arg boardOrder:arg boardDegree:arg reservedGain:arg => ((choices ((namedSuccessor).operandOrdinal (dateInput).operand (DescentRetainedRangeDigits.page f)
  (jj j) (xx x) (nn boardOrder))).amount (hh boardDegree) (gg reservedGain)).val
local notation "hit" => DatePorts.slotAt Rports B.next after_ order_ places
local notation "amountRoom" => DateInputs.named_amount_rooms G S board k tail age p f reservedGain drift degree payload e previous M nextM
  C packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
  previousArguments initial prepared sceneRoom ready

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
omit [Fintype X] in
include rangeRows won origins census in
/-- A missing source node at a valid retained host reads zero for each of its three digits. -/
theorem DateInputs.registered_primary_vacant (size : directorySize)
    (x : Fin (spanLayout).blocks) (j : Fin (spanLayout).operands) (h : Fin (spanLayout).hosts) (g : Fin (spanLayout).groups)
    (n : Fin (spanLayout).nodes) (present : h.val<Fintype.card B.next.V)
    (absent : hit x n h g=none)
    (keep : (dateInput).menu.keep ((C₀).placement.shape (denseAt size ⟨h.val,present⟩))=true)
    (axis : Fin 3) : digit axis j x n h g=0:=by
  have packed:=amountRoom
  have public_:=DateInputs.public_rows_of_origins (B:=B) drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom degreeAt ready inputMem capAt origins
  obtain ⟨values,published,_⟩:=public_ size (xx x)
  have reported:=DateInputs.range_panel_primary_empty (F:=F) (X:=X) (d:=d) (abits:=abits) (W:=W) (G:=G) (q:=q) (ε:=ε) (S:=S)
    (k:=k) (age:=age) (z:=z) (wire:=wire) (hist:=hist) (D:=D) (n:=boardOrder) (h:=boardDegree) (C:=C) (f:=f) (g:=reservedGain)
    (cut:=cut) (tail:=tail) (p:=p) (input:=input) (ctl:=ctl) (B:=B)
    (drift:=drift) (degree:=degree) (payload:=payload) (e:=e) (previous:=previous) (M:=M)
    (nextM:=nextM) (oldLanes:=oldLanes) (primitiveLanes:=primitiveLanes) (printedBits:=printedBits)
    (venue:=venue) (io:=io) (floor:=floor) (w:=w) (fitsStencil:=fitsStencil) (fitsSigned:=fitsSigned)
    (fitsCut:=fitsCut) (count:=count) (previousMeta:=previousMeta) (previousArguments:=previousArguments)
    (initial:=initial) (prepared:=prepared) (sceneRoom:=sceneRoom) (degreeAt:=degreeAt) (capAt:=capAt)
    (ready:=ready) (archived:=oldValues) (μ:=μ) (measured:=measured) (actors:=actorMem) (oldA:=oldA) (num:=oldNum) (hp:=hp)
    (whole:=whole) (ports:=Rports) (places:=places) (block:=x) (node:=n) (rack:=h) (group:=g)
    (present:=present) (absent:=absent) (size:=size) (requests:=rangeRows) (won:=won)
    (total:=total_) (oldBlocks:=rfl) (oldGroups:=rfl)
    (original:=fun geo dim=>census geo (cast (congrArg DescentGL.Layout dim) μ) ((cast_heq _ μ).trans won))
    (x₀:=xx x) (arg:=jj j) (newNode:=nn n) (rh:=hh h) (rg:=gg g)
    (blockAt:=rfl) (nodeAt:=rfl) (hostAt:=rfl) (groupAt:=rfl)
    (values:=values) (published:=published) (small:=small)
    (choice:=fun pageIndex=>choices ((namedSuccessor).operandOrdinal (dateInput).operand pageIndex (jj j) (xx x) (nn n)))
    (live:=ready.placed.lanes) (bus:=packed.2.1) (lane:=packed.2.2) keep axis
  exact reported

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
omit [Fintype X] in
include rangeRows origins in
/-- All three physical digits vanish beyond the real reset roster. -/
theorem DateInputs.registered_exterior_span
    (x : Fin (spanLayout).blocks) (j : Fin (spanLayout).operands) (h : Fin (spanLayout).hosts) (g : Fin (spanLayout).groups)
    (n : Fin (spanLayout).nodes) (outside : Fintype.card B.next.V≤h.val) (axis : Fin 3) :
    digit axis j x n h g=0:=by
  have packed:=amountRoom
  exact DateInputs.range_panel_outside (F:=F) (X:=X) (d:=d) (abits:=abits) (W:=W) (G:=G) (q:=q) (ε:=ε) (S:=S)
    (k:=k) (age:=age) (z:=z) (wire:=wire) (hist:=hist) (D:=D) (n:=boardOrder) (h:=boardDegree) (C:=C) (f:=f) (g:=reservedGain)
    (cut:=cut) (tail:=tail) (p:=p) (input:=input) (ctl:=ctl) (B:=B)
    (drift:=drift) (degree:=degree) (payload:=payload) (e:=e) (previous:=previous) (M:=M)
    (nextM:=nextM) (oldLanes:=oldLanes) (primitiveLanes:=primitiveLanes) (printedBits:=printedBits)
    (venue:=venue) (io:=io) (floor:=floor) (w:=w) (fitsStencil:=fitsStencil) (fitsSigned:=fitsSigned)
    (fitsCut:=fitsCut) (count:=count) (previousMeta:=previousMeta) (previousArguments:=previousArguments)
    (initial:=initial) (prepared:=prepared) (sceneRoom:=sceneRoom) (dd:=degreeAt) (cd:=capAt)
    (ready:=ready) (inputMem:=inputMem) (archived:=oldValues) (μ:=μ) (measured:=measured) (actors:=actorMem) (requests:=rangeRows) (issued:=origins)
    (block:=xx x) (node:=nn n) (arg:=jj j) (rh:=hh h) (rg:=gg g) (small:=small)
    (choice:=fun pageIndex=>choices ((namedSuccessor).operandOrdinal (dateInput).operand pageIndex (jj j) (xx x) (nn n)))
    (live:=ready.placed.lanes) (bus:=packed.2.1) (lane:=packed.2.2) (padding:=outside) (axis:=axis)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
omit [Fintype X] in
include rangeRows won origins census in
/-- An unoccupied block has no fresh argument. A selected retained host gets its zero
from the absence of the corresponding original argument node. -/
theorem DateInputs.registered_unoccupied_span
    (x : Fin (spanLayout).blocks) (j : Fin (spanLayout).operands) (h : Fin (spanLayout).hosts) (g : Fin (spanLayout).groups)
    (n : Fin (spanLayout).nodes) (present : h.val<Fintype.card B.next.V)
    (missing : ¬∃site,DescentPaidResidentCount.occupies B.next.placement (Equiv.refl _) B.next.vertex
      ⟨h.val,present⟩ (g.cast places.groups.symm) (x.cast (congrArg (2^·) places.radix.symm)) site)
    (absent : hit x n h g=none) (axis : Fin 3) : digit axis j x n h g=0:=by
  have packed:=amountRoom
  have empty_:=actualBit_no_site B B.next.valid.host (hh h) (gg g) (xx x) present missing
  rcases DateInputs.range_panel_inactive (F:=F) (X:=X) (d:=d) (abits:=abits) (W:=W) (G:=G) (q:=q) (ε:=ε) (S:=S)
    (k:=k) (age:=age) (z:=z) (wire:=wire) (hist:=hist) (D:=D) (n:=boardOrder) (h:=boardDegree) (C:=C) (f:=f) (g:=reservedGain)
    (cut:=cut) (tail:=tail) (p:=p) (input:=input) (ctl:=ctl) (B:=B)
    (drift:=drift) (degree:=degree) (payload:=payload) (e:=e) (previous:=previous) (M:=M)
    (nextM:=nextM) (oldLanes:=oldLanes) (primitiveLanes:=primitiveLanes) (printedBits:=printedBits)
    (venue:=venue) (io:=io) (floor:=floor) (w:=w) (fitsStencil:=fitsStencil) (fitsSigned:=fitsSigned)
    (fitsCut:=fitsCut) (count:=count) (previousMeta:=previousMeta) (previousArguments:=previousArguments)
    (initial:=initial) (prepared:=prepared) (sceneRoom:=sceneRoom) (dd:=degreeAt) (cd:=capAt)
    (ready:=ready) (inputMem:=inputMem) (archived:=oldValues) (μ:=μ) (measured:=measured) (actors:=actorMem) (requests:=rangeRows) (issued:=origins)
    (block:=xx x) (node:=nn n) (arg:=jj j) (rh:=hh h) (rg:=gg g) (small:=small)
    (choice:=fun pageIndex=>choices ((namedSuccessor).operandOrdinal (dateInput).operand pageIndex (jj j) (xx x) (nn n)))
    (live:=ready.placed.lanes) (bus:=packed.2.1) (lane:=packed.2.2) (masked:=empty_) (axis:=axis) with zero|retained
  · exact zero
  · obtain ⟨alive,hosts_,shapes_,keep⟩:=retained
    exact DateInputs.registered_primary_vacant (B:=B) (rangeRows:=rangeRows) (won:=won)
      (origins:=origins) (census:=census) (oldNum:=oldNum) (places:=places) (axes:=axes) (choices:=choices)
      (size:=congrArg₂ Nat.mul hosts_ shapes_) (x:=x) (j:=j) (h:=h) (g:=g) (n:=n)
      (present:=present) (absent:=absent) (keep:=keep) (axis:=axis)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI

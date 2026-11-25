import OAI.Hierarchy.DescentPurchasedStageInstance
import OAI.Hierarchy.DescentPurchasedTerminalArchive
import OAI.Hierarchy.DescentNamedFinalOperandHeaders
import OAI.Hierarchy.DescentNamedFinalSitePrinted

namespace OAI
/-! # Operand cells of the final purchased site image -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentDatedAddressBook Chronology Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open private mountedArchiveResult from OAI.Hierarchy.DescentPurchasedTerminalArchive
noncomputable section
set_option maxHeartbeats 3800000
set_option maxRecDepth 12000
set_option cleanup.letToHave false
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
variable (menu : RegisterTimeline.Menu n d) (k w : ℕ) (prior final : RegisterTimeline.Position)
local notation "dateMachine" => PhysicalReset.scheduled G S menu.board k menu.tail (S.length-1) menu.p menu.f menu.gain
  menu.drift menu.degreeLimit menu.payload menu.ordinary menu.op (S.firstWidth G.b menu.p) (S.grainAt G.b menu.p 0)
  prior.ports.operandLanes prior.ports.roleLanes prior.ports.venue prior.ports.io.wire prior.ports.io.roster
  (prior.ports.priorStart k prior.floor)
local notation "beginFloor" => (dateMachine).stageStart (prior.ports.priorStart k prior.floor)
private theorem restoreRoleArchiveInput (want : DatePorts → Memory w → Prop) {base finish : ℕ}
    (mount : RoleMount w base finish) (first count : ℕ) (source : ℕ → ℕ) (heap : Memory w)
    (result : mountedArchiveResult G S menu k w prior final want mount first count source heap) :
    ∃ restored : (dateMachine).DateInputs beginFloor w,
      want (DatePorts.reset dateMachine beginFloor restored) (mount.phase.image (DescentLowCountBook.output first source heap count)) := by
  obtain ⟨space, _, printed⟩ := result
  exact ⟨DatePorts.resetInputs G S menu.board k menu.tail (S.length-1) menu.p menu.f menu.gain menu.drift
    menu.degreeLimit menu.payload menu.ordinary menu.op (S.firstWidth G.b menu.p) (S.grainAt G.b menu.p 0)
    prior.ports prior.floor w space, printed⟩


end
end Hierarchy.DescentSixParty.SeedNamed


namespace Hierarchy.DescentSixParty.SeedNamed
open DescentKernelHistory DescentBundleHistory DescentLocalPrivateNames DescentTerminalPointerIssue
/-- Relabeling scalar tags preserves the occupied node and argument coordinates used by a stored header. -/
theorem argumentHeaderAfterRetag {A U V : Type} {bits : A → ℕ} {N K p : ℕ}
    {source : BitRecipe U A bits} (shape : Shape p source) (label : U → V) (hp : 0 < p)
    (number : source.Node ↪ ℕ) (nodes : Fintype.card source.Node ≤ N)
    (arity : ∀ u, (shape.recipe hp).arity u ≤ K)
    (decode : ℕ → ℕ → ℕ) (bank : Fin 4 → Fin K → ℕ) (expect : source.Node → ℕ → Fin 4 → ℕ)
    (stored : ∀ a : Slot (shape.recipe hp), ∀ f : Fin 4,
      decode (row (shape.recipe hp) number nodes a.1).val (bank f (a.2.castLE (arity a.1))) = expect a.1 a.2.val f)
    (a : Slot ((shape.retag label).recipe hp)) (f : Fin 4) :
    decode (row ((shape.retag label).recipe hp) number nodes a.1).val (bank f (a.2.castLE (arity a.1))) =
      expect a.1 a.2.val f := stored ⟨a.1, ⟨a.2.val, a.2.isLt⟩⟩ f
end Hierarchy.DescentSixParty.SeedNamed

namespace Hierarchy.DescentSixParty.SeedNamed
open CorrectionFrame
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalGraphPositions DescentTerminalGraphVolume DescentTerminalCableOrder DescentKernelHistory
open DescentBundleHistory DescentPrimitivePalette DescentRotor DescentResetGates CorrectionBatch
open DescentTerminalBinReaddress DescentTerminalPorts Computability.BorderVNP.Crossing
open DescentTerminalEmitter DescentTerminalEmitter.Branch DescentTerminalChipRuntime
open DescentTerminalVertexFields DescentTerminalHeaderScatter DescentTerminalSiteShelves
open DescentTerminalScalarTransposes DescentTerminalDenseWindow DescentTerminalRecipeRows
open DescentTerminalScalarPadded DescentTerminalCompiledPrefix DescentEpochTagKeys
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical BigOperators
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin Branch.archive Branch.bundleShape

set_option cleanup.letToHave false

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g W q piece : ℕ}
local notation "p" => W*piece
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0<(W*piece)) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
variable (c : ((Epochs.finish G _ _ ((normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten)).choose)).Choice)
local notation "b" => issued X G S ordinary reset branch positive room shorten c
local notation "s" => S.firstWidth G.b p
local notation "Z" => S.grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
local notation "U" => Label G s Z rot
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "cap" => NativeBranch.privateSlotCapacity G S R
local notation "nodeCap" => S.epochPower^S.localTokenExponent

variable {j rest : ℕ} (base : S.baseGroups=2^tail) (width : S.groupWidth k tail 0+k=j+(j+rest))
variable (age : 0<S.height) (wFit : NativeBranch.binLimit (k:=k) S ≤ W)
  (qFit : NativeBranch.localLimit G S ≤ q) (qh : 0<q)

open DescentExterior Computability.VPVNP.RAMSerialization DescentTerminalExteriorPackets DescentTerminalPublicIdentity
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall DescentPackedProfileTape
open DescentSeedRoot DescentExteriorShelf DescentTerminalPrimitiveArena
local notation "E₀" => Fintype.card (Port P X.width)
local notation "H₀" => S.hostSize S.length
variable (template:DescentTerminalCompiledPrefix.Shape) (sitesPositive:0<(S.hostSize S.length)) (rawWords headerRows paidRows:ℕ)
local notation "cfg" => Branch.exteriorShape template E₀ j rest s rawWords headerRows H₀ sitesPositive
variable (pool : terminalPool X G S (W*piece) q W n h C f g ≤ ((Branch.exteriorShape template (Fintype.card (Port P X.width)) j rest (S.firstWidth G.b (W*piece)) rawWords headerRows (S.hostSize S.length) sitesPositive)).terminal.pool)
    (raw : terminalRawRows X G S (W*piece) q n h C f g ≤ ((Branch.exteriorShape template (Fintype.card (Port P X.width)) j rest (S.firstWidth G.b (W*piece)) rawWords headerRows (S.hostSize S.length) sitesPositive)).terminal.plane.rawRows)
local notation "groupsAt" => S.groupCount S.length
open DescentTerminalCompiledPrefix.AddressPlan DescentTerminalEmitter.Compact
open DescentTerminalLocalPortBook DescentTerminalSpanBook DescentTerminalBinPack
open DescentTerminalPreflightSpace ThreeFlat.RAM PhysicalProcedure

open DescentPackedEpochFold DescentExteriorMatrixUpdate DescentPackedSeed DescentSeedRoot
open ThreeFlat Routing Diagonal
variable {w : ℕ}
local notation "fmt" => Branch.geometryFormat G S k g p tail q R rot headerRows paidRows
open DescentTerminalGrainProfiles DescentTerminalDenseHeaderBoot DescentSortedRoster
open DescentTerminalLocalPortBook.Rasters DescentPackedColony



open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentResetInvoice CorrectionBatch
open DescentSixParty.SeedNamed.Branch DescentExteriorReplay DescentTerminalFixedSlices
open DescentTerminalPointerDigits DescentTerminalCombinedRole DescentSIMDLookup DescentPackedColony
open ThreeFlat.Routing CallPool DescentColonies DescentActorRaster DescentColonies.SplitRAM
open DescentTerminalRoleTables DescentTerminalPointerIssue
variable {boardDegree:ℕ} (board : NonlinearExpanders.Graph n boardDegree) (dateAge dateDegree datePayload : ℕ)
    (ordinaryAt : ℕ→Dated.Ordinary) (operandLanes primitiveLanes : ℕ) (previousDate : StageVenueTail.Date)
    (priorAddress : ℕ→ℕ→Bank) (rosterBank : Bank) (datedFloor replayBase matrixTable : ℕ)
    (dateTag : ℕ→Bool) (dateRotation : ℕ→ℕ) (snapshots : Snapshots k) (roleBase : ℕ)
    (past : Memory w) (start count : ℕ) (source : ℕ → ℕ) (mount : Chronology.RoleMount w roleBase replayBase)
variable (mountedMemory_ : Memory w)
local notation "datedMem" => mountedMemory_

local notation "dateSpec" => preflightSpec X G S k g p tail (geometryFormat G S k g p tail q R rot headerRows paidRows)
local notation "datePorts" => Fintype.card (Port P X.width)
local notation "datePhase" => Phase.scheduled G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
  operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
local notation "dateOut" => (datePhase).output
local notation "dateOrigin" => (datePhase).dateBase
local notation "dateMachine" => PhysicalReset.scheduled G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
  s Z operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
variable (dateInput : ((PhysicalReset.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset)   (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).DateInputs (((PhysicalReset.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset)   (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).stageStart datedFloor) w)
local notation "earlierPages" => PhysicalReset.FinalInputs.predecessor dateInput
local notation "dateCalendar" => replayCalendar X S k tail j rest snapshots
local notation "earlyFloor" => DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail replayBase j rest s datePorts
local notation "earlyImage" => DescentExteriorMatrixUpdate.Calendar.earlyImage S k tail replayBase dateTag dateRotation j rest s datePorts matrixTable
local notation "sliceEnd" => (datePhase).stop earlyFloor
local notation "lookupBase" => (dateCalendar).packetEnd sliceEnd
local notation "lookupPage" => (dateSpec).scanPages lookupBase q
local notation "censusBase" => (lookupPage).stop
local notation "dateVenue" => (dateOut).venue.next
local notation "dateHardware" => (dateOut).receiver
local notation "dateShops" => (dateSpec).scalar.shops
local notation "dateBlocks" => (dateSpec).scalar.blocks
local notation "blockCast" => (rfl : dateBlocks=(dateHardware).blocks)
local notation "paidBank" => fun x:Fin dateBlocks=>(dateOut).terminalPaid dateOrigin x.val
local notation "actorBank" => fun x:Fin dateBlocks=>(dateOut).terminalActor dateOrigin x.val
local notation "wingBank" => fun (x:Fin dateBlocks) (a:Fin (2*(dateSpec).cap))=>(dateOut).terminalWing dateOrigin x.val a.val
local notation "peerBank" => (dateOut).terminalPeer dateOrigin
local notation "dateColors" => DescentPrimitivePalette.colors G s Z rot
local notation "roleBankBits" => fun f:Fin 6=>DescentTerminalCombinedRole.width dateColors (max 8 (2^S.capGain))
  cap p R f*(S.epochPower^S.localTokenExponent)*(dateSpec).groups
local notation "atomBits" => Nat.clog 2 (nodeCap+1)
local notation "operandWidths" => (⟨atomBits,Nat.clog 2 (cap+1),fun _=>DescentOperandWidth.recordBits G S k tail R 3 p,some nodeCap⟩:Widths)
local notation "terminalPin" => DescentExterior.terminalPin (S.groupWidth k tail 0+k) (S.groupWidth k tail S.length+k) (k*S.length)
local notation "publicCell" => DescentTerminalPointerDigits.publicCell («cap»:=(dateSpec).cap) (N:=nodeCap) (A:=cap)
  (d:=(dateSpec).scalar.pointerBits) 3 q G.b (poolBatchCount (s*1) p) (k*S.length) (dateSpec).groups operandWidths
local notation "privateCell" => DescentTerminalPointerDigits.output (dateSpec).cap nodeCap cap 3 (dateSpec).groups
  (dateSpec).scalar.pointerBits (Nat.clog 2 (q+cap+1)) q G.b (poolBatchCount (s*1) p) operandWidths terminalPin
local notation "roleBanks" => DescentTerminalRoleTables.role roleBankBits ((datePhase).banks earlyFloor) roleBase
local notation "arityBanks" => DescentTerminalRoleTables.arity roleBankBits ((datePhase).banks earlyFloor) roleBase
local notation "matrixFloor" => DescentExteriorMatrixUpdate.Calendar.stop S k tail replayBase+S.length
local notation "pointerBank" => fun (f:Fin 4) (j:Fin (dateOut).argumentSlots) (x:Fin dateBlocks) =>
  (dateOut).terminalPointers dateOrigin f j (x.cast blockCast)
local notation "oldOperands" => DescentTerminalOperandRepack.padded (K:=cap) pointerBank paidBank
local notation "operandChart" => ((dateSpec).pointerPages censusBase matrixFloor oldOperands wingBank).address (N:=nodeCap)
variable (replayRoom : Branch.scheduledPreflightStop X G S (tail:=tail) g (W*piece) q
  (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows board dateAge f
  dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
  j rest (S.firstWidth G.b (W*piece)) replayBase snapshots < 2^w)
local notation "dateEntry" => (dateCalendar).memory sliceEnd censusBase replayRoom ((datePhase).memory earlyFloor (earlyImage datedMem))
local notation "primitiveImage_" => (dateSpec).primitiveSnapshot (base:=censusBase) (w:=w) (q:=q) («p»:=p) (nd:=atomBits)
  (nodes:=nodeCap) (hidden:=cap) (args:=cap) (oldPaid:=paidBank) (actor:=actorBank) (first:=roleBanks) (second:=arityBanks)
  («chart»:=operandChart) (f0:=publicCell) (f7:=privateCell) ((lookupPage).image dateEntry)
local notation "datedDecoder" => Branch.decodeBook S G base ordinary.radix p q 3
  (dateSpec).cap (dateSpec).printBits (by decide)
local notation "bookImage_" => (dateSpec).bookSnapshot (base:=censusBase) (peer:=peerBank) (wing:=wingBank)
  (w:=w) (q:=q) («p»:=p) (nd:=atomBits) (nodes:=nodeCap) (hidden:=cap) (args:=cap)
  (oldPaid:=paidBank) (actor:=actorBank) (first:=roleBanks) (second:=arityBanks) («chart»:=operandChart)
  (f0:=publicCell) (f7:=privateCell) (decode:=datedDecoder) ((lookupPage).image dateEntry)
local notation "dateHomes" => (dateCalendar).homes sliceEnd
local notation "postEntry_" => Branch.postEarlyPreflightMemory X G S base ordinary.radix g p q R rot headerRows paidRows
  j rest s replayBase datePhase snapshots blockCast roleBase peerBank paidBank actorBank wingBank replayRoom
  (earlyImage datedMem)
local notation "bookControl" x => portTable (G:=4) («V»:=(x).vertices) (M:=(x).vertices*(x).arguments)
  (A:=(x).arguments) (a:=Book.tokenBits ((x).vertices*(x).arguments)) q
local notation "postBook" x => (x).afterSiteControls censusBase q p peerBank wingBank
  (((x).scanPages lookupBase q).total) (((x).scanPages lookupBase q).modulo) dateHomes
  (((x).scanPages lookupBase q).boundaries)
  (((x).controls censusBase).after (bookControl x) (Book.expression ((x).parts censusBase)) bookImage_)

local notation "physicalRows" => PrimitiveDateRows (q:=q) (j:=j) (rest:=rest) (W:=W) (piece:=piece) (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive)
    (room:=room) (shorten:=shorten) (c:=c) (board:=board) (dateAge:=dateAge) (dateDegree:=dateDegree)
    (datePayload:=datePayload) (ordinaryAt:=ordinaryAt) (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes)
    (previousDate:=previousDate) (priorAddress:=priorAddress) (rosterBank:=rosterBank) (datedFloor:=datedFloor)
    (replayBase:=replayBase) (matrixTable:=matrixTable) (dateRotation:=dateRotation)
    (snapshots:=snapshots) (roleBase:=roleBase) (dateInput:=dateInput) («datedMem»:=datedMem)
    (headerRows:=headerRows) (paidRows:=paidRows)

local notation "actualRoster" => (b).target.terminalRoster (b).target.valid.host
local notation "originalTier" => Branch.preflight_caps (tail:=tail) X G S b fmt
open DescentPackedColony


open DescentTerminalChronologicalBooks
local notation "homeOrd" => Branch.leafOrder X G S b positive base width
local notation "trueLeaf" => normalizedLeaf X G S ordinary reset branch positive room shorten c
  base width age wFit qFit qh cfg pool raw
local notation "liveCodec" => DescentPrimitivePalette.codec (G:=G) («s»:=s) («Z»:=Z) rot
local notation "allTags" => DescentBundleTagKeys.capacity dateColors (max 8 (2^S.capGain)) cap p R
local notation "allCodes" => DescentBundleTagKeys.codec liveCodec (max 8 (2^S.capGain)) cap p R
local notation "atSite" => fun v=>(((trueLeaf).shape v).recipe positive).restricted
local notation "liveRec" => DescentTerminalBundleRows.recipes homeOrd atSite positive (trueLeaf).birth (allCodes).store
local notation "liveRanks" => DescentTerminalChronologicalChip.charts (arity:=max 8 (2^S.capGain)) (groups:=cap) (stride:=R)
  ((last).state c).graph (trueLeaf).home (trueLeaf).native (trueLeaf).external (trueLeaf).nodes (trueLeaf).ops
  (trueLeaf).bit (trueLeaf).shape positive (trueLeaf).birth (trueLeaf).hidden liveCodec
local notation "hiddenFit" i:arg v:arg => (DescentTerminalRestrictedRows.hidden_bound (trueLeaf).bit (trueLeaf).shape
  positive ((homeOrd).node i v)).trans ((trueLeaf).countsFit ((homeOrd).node i v))
local notation "nodeFit" i:arg v:arg => (trueLeaf).atoms ((homeOrd).node i v)
local notation "argFit" i:arg v:arg u:arg => ((((trueLeaf).shape ((homeOrd).node i v)).recipe_refs positive u).symm ▸
  (trueLeaf).refs ((homeOrd).node i v) u : (liveRec i v).arity u ≤ cap)
local notation "realPage" => MaskAllocation.shelf (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) («p»:=p)
  (groups:=groupsAt) ((dateSpec).channels censusBase) ((dateSpec).maskBase censusBase)
local notation "cells" => (dateSpec).channels censusBase
local notation "maskStart" => (dateSpec).maskBase censusBase
local notation "slotNode" home:arg site:arg u:arg => (DescentTerminalChronologicalBooks.ordinal ((liveRanks home).atom site) u).castLE (nodeFit home site)
local notation "siteAddr" home:arg site:arg => finProdFinEquiv
  (((b).target.placement.pos ((homeOrd).node home site)).1,(b).target.placement.block ((homeOrd).node home site))
local notation "siteWord" home:arg site:arg key:arg =>
  venueField (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
    (cellAt (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
      (measured (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
        realPage primitiveImage_ home) (siteAddr home site)) key
local notation "paidPackets_" => WideMeasuredPackets (W:=W) (piece:=piece) (q:=q) (j:=j) (rest:=rest) (w:=w) (X:=X) (G:=G) (S:=S) (ordinary:=ordinary)
  (reset:=reset) (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (c:=c)
  (base:=base) (width:=width) (headerRows:=headerRows) (paidRows:=paidRows)
  (begin_:=censusBase) (peer:=peerBank) (old:=wingBank) (org:=lookupBase) (homes:=dateHomes)
  (primitive:=primitiveImage_) (m:=bookImage_)
open DescentLocalPrivateNames

local notation "observedGrid" => (b).target.placement
local notation "observedNames" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=groupsAt)) ((b).target.vertex.trans Fin.valEmbedding))
local notation "observedNative" => (b).target.order.trans Fin.valEmbedding
local notation "observedRecipe" v:arg => ((trueLeaf).shape v).recipe positive
local notation "rowCount" v:arg => (trueLeaf).atoms v
local notation "rowArity" v:arg u:arg => (((trueLeaf).shape v).recipe_refs positive u).symm ▸ (trueLeaf).refs v u
local notation "archiveNames" => Branch.localNodes X G S b positive
local notation "rowPos" v:arg u:arg => DescentTerminalPointerIssue.row (observedRecipe v) ((trueLeaf).birth v) (rowCount v) u
local notation "oldPtr" v:arg a:arg => Reached.argumentPointer (b).target (Branch.archive X G S b positive).bit
  archiveNames (Branch.bundleShape X G S b positive (Nat.le_max_left 1 (max reset.bitsR (C*reset.bitsR)))) positive
  (fun z=>z.1.val) (dateOut).argumentSlots ⟨v,a.1⟩ a.2.val

local notation "originalWordField" form:arg => form
  (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive)
  (room:=room) (shorten:=shorten) (c:=c) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit)
  (qh:=qh) (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords)
  (headerRows:=headerRows) (paidRows:=paidRows) (pool:=pool) (raw:=raw) (board:=board) (dateAge:=dateAge)
  (dateDegree:=dateDegree) (datePayload:=datePayload) (ordinaryAt:=ordinaryAt)
  (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previousDate:=previousDate)
  (priorAddress:=priorAddress) (rosterBank:=rosterBank) (datedFloor:=datedFloor) (replayBase:=replayBase)
  (matrixTable:=matrixTable) (dateTag:=dateTag) (dateRotation:=dateRotation) (snapshots:=snapshots)
  (roleBase:=roleBase) («datedMem»:=datedMem) (replayRoom:=replayRoom)


open Chronology
set_option maxHeartbeats 1800000 in
private theorem paidStoredOperandHeader
    (originalInput : (dateMachine).DateInputs ((dateMachine).stageStart datedFloor) w)
    (previous : FinalPointerArchive X G S ordinary reset branch positive room shorten w c
      (DatePorts.reset dateMachine ((dateMachine).stageStart datedFloor) originalInput) past)
    (sizes : DescentOperandWidth.recordBits G S k tail R dateDegree p = DescentOperandWidth.recordBits G S k tail R 3 p)
    (early : start + count ≤ dateOrigin) (done_ : (dateOut).finalEnd dateOrigin ≤ roleBase)
    (space : (dateOut).metadataEnd dateOrigin < 2^w)
    (single : chunks (dateOut).receiver.groups (dateOut).receiver.lanes = 1)
    (wide : ((dateOut).nodeBits * (dateOut).nodes) * (dateOut).receiver.lanes ≤ w)
    (previousFits : ∀ v, ∀ u, (observedRecipe v).arity u ≤ (dateOut).argumentSlots)
    (v : ((last).state c).graph.Site) (a : DescentLocalPrivateNames.Slot (observedRecipe v)) (f₀ : Fin 4) :
    (operandWidths).nodeDigit (DescentOperandWidth.recordBits G S k tail R 3 p)
      (rowPos v a.1).val ((observedGrid).pos v).1.val
      ((mount.phase.image (DescentLowCountBook.output start source past count))
        ((pointerBank f₀ (a.2.castLE (previousFits v a.1)) ((observedGrid).block v)).base +
        ((b).target.home v).val)).val = (oldPtr v a).header f₀ := by
  have slots := Branch.final_argument_capacity X G S b positive
    (Nat.le_max_left 1 (max reset.bitsR (C*reset.bitsR))) age branch
  let shape₀ := (Branch.bundleShape X G S b positive (Nat.le_max_left 1 (max reset.bitsR (C * reset.bitsR)))).sites v
  let color := (Palette.atLeaf X G S ordinary reset branch positive room shorten c).code
  let number := (Branch.localNodes X G S b positive v).toEmbedding.trans Fin.valEmbedding
  let word (idx cell : ℕ) := (operandWidths).nodeDigit (DescentOperandWidth.recordBits G S k tail R 3 p)
    idx ((b).target.placement.pos v).1.val
    ((mount.phase.image (DescentLowCountBook.output start source past count)) (cell + ((b).target.home v).val)).val
  let terminalBank (priorField : Fin 4) (i : Fin (dateOut).argumentSlots) :=
    ((dateOut).terminalPointers dateOrigin priorField i ((b).target.placement.block v)).base
  let header (u : (shape₀.recipe positive).Node) (i : ℕ) (opcode : Fin 4) :=
    (Reached.argumentPointer (b).target (Branch.archive X G S b positive).bit
      (Branch.localNodes X G S b positive) (Branch.bundleShape X G S b positive
        (Nat.le_max_left 1 (max reset.bitsR (C*reset.bitsR)))) positive
      (fun z=>z.1.val) (dateOut).argumentSlots ⟨v,u⟩ i).header opcode
  refine argumentHeaderAfterRetag shape₀ color positive number (Branch.site_nodes X G S b positive age v)
    (slots v) word terminalBank header ?_ a f₀
  intro originalSlot digitIndex
  exact final_operand_headers_of_width (X:=X) (G:=G) (S:=S) (ordinary:=ordinary)
    (reset:=reset) (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (c:=c)
    (board:=board) (dateAge:=dateAge) (dateDegree:=dateDegree) (datePayload:=datePayload)
    (ordinaryAt:=ordinaryAt) (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes)
    (previousDate:=previousDate) (priorAddress:=priorAddress) (rosterBank:=rosterBank) (datedFloor:=datedFloor)
    (dateInput:=originalInput) (past:=past) (capture:=start) (source:=source)
    (size:=count) (mount:=mount) (reached:=previous) (sizes:=sizes)
    (early:=early) (done_:=done_) (space:=space) (single:=single) (wide:=wide)
    (v:=v) (nn:=Branch.site_nodes X G S b positive age v) (oldFits:=slots v) (a₀:=originalSlot) (f₀:=digitIndex)
private def mountedOperandProperty {rawPeers} (_date : physicalRows rawPeers)
    (_acquired : paidPackets_)
    (_matrixRead : primitiveImage_ matrixFloor = ((DescentExterior.matrixCode
      (Branch.pinSpine X G S b positive base).matrix).val : Computability.VPVNP.BurstRAM.Word w))
    (originalInput : (dateMachine).DateInputs ((dateMachine).stageStart datedFloor) w)
    (_previous : FinalPointerArchive X G S ordinary reset branch positive room shorten w c
      (DatePorts.reset dateMachine ((dateMachine).stageStart datedFloor) originalInput) past)
    (_sizes : DescentOperandWidth.recordBits G S k tail R dateDegree p =
      DescentOperandWidth.recordBits G S k tail R 3 p)
    (_early : start+count ≤ dateOrigin)
    (_done_ : (dateOut).metadataEnd dateOrigin ≤ roleBase)
    (_replayFits : replayBase < 2^w)
    (_wasMounted : mountedMemory_ = mount.phase.image (DescentLowCountBook.output start source past count))
    (_arities : originalWordField OriginalSiteArityWords) :
    Prop := originalWordField OriginalSiteArgumentWords

private theorem registeredHeaderRange (assignment : DescentDatedAddressBook.ResetOutput) (origin : ℕ)
    {bits base roof : ℕ} (installed : Chronology.RoleMount bits base roof)
    (closed : assignment.metadataEnd origin ≤ base) (space : roof < 2^bits) :
    assignment.finalEnd origin ≤ base ∧ assignment.metadataEnd origin < 2^bits := by
  have cuts := assignment.terminal_order origin
  exact ⟨(cuts.1.trans (cuts.2.1.trans cuts.2.2)).trans closed, closed.trans_lt (installed.placed.trans_lt space)⟩
set_option maxHeartbeats 3000000 in
private theorem mountedPhysicalOperands {rawPeers} (date : physicalRows rawPeers)
    (originalInput : (dateMachine).DateInputs ((dateMachine).stageStart datedFloor) w)
    (previous : FinalPointerArchive X G S ordinary reset branch positive room shorten w c
      (DatePorts.reset dateMachine ((dateMachine).stageStart datedFloor) originalInput) past)
    (sizes : DescentOperandWidth.recordBits G S k tail R dateDegree p =
      DescentOperandWidth.recordBits G S k tail R 3 p)
    (early : start+count ≤ dateOrigin)
    (done_ : (dateOut).metadataEnd dateOrigin ≤ roleBase)
    (replayFits : replayBase < 2^w)
    (wasMounted : mountedMemory_ = mount.phase.image (DescentLowCountBook.output start source past count))
    (previousFits : ∀ (v : ((last).state c).graph.Site), ∀ u, (observedRecipe v).arity u ≤ (dateOut).argumentSlots) :
    ∀ (v : ((last).state c).graph.Site), ∀ a : DescentLocalPrivateNames.Slot (observedRecipe v), ∀ f₀ : Fin 4,
    (operandWidths).nodeDigit (DescentOperandWidth.recordBits G S k tail R 3 p)
      (rowPos v a.1).val ((observedGrid).pos v).1.val
      (mountedMemory_ ((pointerBank f₀ (a.2.castLE (previousFits v a.1)) ((observedGrid).block v)).base +
        ((b).target.home v).val)).val = (oldPtr v a).header f₀ := by
  have one:=Phase.scheduled_one G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
    operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor date.lastDate base date.signedWidth
  have finiteRange := registeredHeaderRange dateOut dateOrigin mount done_ replayFits
  have packed : ((dateOut).nodeBits*(dateOut).nodes)*(dateOut).receiver.lanes≤w :=by
    have capBits:=DescentTerminalPointerDigits.input_bounds (S.groupCount S.length) nodeCap
      (S.groupWidth k tail 0+k) (k*S.length) (2^(8+S.capGain*S.length))
      (Nat.clog 2 (nodeCap+1)) (Nat.clog 2 (cap+1)) (DescentOperandWidth.recordBits G S k tail R 3 p)
      (DescentSignedCableCodec.width 3 (dateSpec).cap)
    have lanes:(dateOut).receiver.lanes=S.groupCount S.length:=date.signedWidth
    change (DescentOperandWidth.recordBits G S k tail R dateDegree p*nodeCap)*(dateOut).receiver.lanes≤w
    rw [sizes,lanes]
    exact capBits.2.2.2.2.1.trans (Branch.final_operand_widths X G S k g p tail q R rot headerRows paidRows censusBase w date.wordRoom).1
  intro v a f₀
  rw [wasMounted]
  have h_ := paidStoredOperandHeader (F:=F) (cp:=cp) (P:=P)
    (k:=k) (cut:=cut) (tail:=tail) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g)
    (W:=W) (piece:=piece) (q:=q) (j:=j) (rest:=rest) (w:=w) (boardDegree:=boardDegree) (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset)
    (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (c:=c)
    (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
    (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows) (paidRows:=paidRows)
    (pool:=pool) (raw:=raw) (board:=board) (dateAge:=dateAge) (dateDegree:=dateDegree)
    (datePayload:=datePayload) (ordinaryAt:=ordinaryAt) (operandLanes:=operandLanes)
    (primitiveLanes:=primitiveLanes) (previousDate:=previousDate) (priorAddress:=priorAddress)
    (rosterBank:=rosterBank) (datedFloor:=datedFloor) (start:=start) (count:=count) (source:=source)
    (past:=past) (mount:=mount) (originalInput:=originalInput) (previous:=previous) (sizes:=sizes)
    (early:=early) (done_:=finiteRange.1) (space:=finiteRange.2) (single:=one) (wide:=packed)
    (roleBase:=roleBase) (replayBase:=replayBase) (previousFits:=previousFits) (v:=v) (a:=a) (f₀:=f₀)
  exact h_

end
end Hierarchy.DescentSixParty.SeedNamed
namespace Hierarchy.DescentSixParty.SeedNamed
open Lean Meta Elab Command
run_cmd modifyEnv fun env => LibrarySuggestions.nameDenyListExt.modifyState env ("mounted_site_argument_words" :: ·)
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

private def argumentBinder (xs : Array Expr) (name : Name) : MetaM Expr := do
  let some x ← xs.findM? (fun x => do return (← x.fvarId!.getDecl).userName.eraseMacroScopes == name) |
    throwError "Missing operand purchase parameter {name}"
  return x

private def fillOperandRows (receipt : ConstantInfo) (xs : Array Expr) (capacity : Option Expr) : MetaM Expr := do
  forallTelescope receipt.type fun bs _ => do
    let mut args := #[]
    for b in bs do
      let bd ← b.fvarId!.getDecl
      let name := bd.userName.eraseMacroScopes
      if name == `v then break
      let a ← if bd.binderInfo.isInstImplicit then pure xs[1]! else
        if name == `previousFits then
          match capacity with
          | some cap => pure cap
          | none => throwError "Missing paid operand capacity"
        else argumentBinder xs name
      args := args.push a
    return mkAppN (mkConst receipt.name (receipt.levelParams.map Level.param)) args

run_cmd liftTermElabM do
  let schema ← getConstInfo ``mountedOperandProperty
  let donor ← getConstInfo ``final_site_arguments
  let slots ← getConstInfo ``final_argument_room
  let reads ← getConstInfo ``mountedPhysicalOperands
  let rec publicNames : Expr → Expr
    | .forallE n t b bi =>
      let key := match n with
        | .str .anonymous s => if ["_date", "_acquired", "_matrixRead", "_previous", "_sizes", "_early", "_done_", "_replayFits", "_wasMounted", "_arities"].contains s then Name.mkSimple (s.drop 1).toString else n
        | _ => n
      .forallE key t (publicNames b) bi
    | e => e
  forallTelescope (publicNames schema.type) fun xs _ => do
    let goal := (schema.value!.beta xs).consumeMData
    unless goal.getAppFn.constName? == some ``OriginalSiteArgumentWords do
      throwError "Expected the original operand property"
    let ws := goal.getAppArgs
    unless ws.size == 61 do throwError "Expected all 61 original physical fields, found {ws.size}"
    let capacity ← fillOperandRows slots xs none
    let earlier ← fillOperandRows reads xs (some capacity)
    let front := ws.extract 0 60
    let params := front ++ #[← argumentBinder xs `dateInput, ws[60]!, ← argumentBinder xs `rawPeers,
      ← argumentBinder xs `date, ← argumentBinder xs `acquired, ← argumentBinder xs `matrixRead,
      capacity, earlier, ← argumentBinder xs `arities]
    let args ← forallTelescope donor.type (fun ps _ => pure ps.size)
    unless args == params.size do throwError "Expected {args} source fields, found {params.size}"
    let ty ← mkForallFVars xs goal
    let value ← mkLambdaFVars xs (mkAppN (mkConst donor.name (donor.levelParams.map Level.param)) params)
    addDecl (.thmDecl {name := `OAI.Hierarchy.DescentSixParty.SeedNamed.mounted_site_argument_words, levelParams := schema.levelParams, type := ty, value := value})
end Hierarchy.DescentSixParty.SeedNamed

namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P → ℕ} {d k wire hist w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C → RunTrace G q ε S k wire hist S.length bits d)
    {n degree : ℕ} (book : Menu n degree) (initial : Position)
local notation "cursor" => calendar (w:=w) traces book initial
local notation "prior" => cursor (S.length-1)
local notation "job" => PhysicalReset.scheduledAtPorts G S book.board k book.tail (S.length-1) book.p book.f book.gain
  book.drift book.degreeLimit book.payload book.ordinary book.op (S.firstWidth G.b book.p) (S.grainAt G.b book.p 0)
  (prior).ports (prior).floor
local notation "addr" => (prior).ports.priorStart k (prior).floor
omit [Fintype P] in
set_option maxRecDepth 8192 in
private theorem capture_before_final_reset (lo size : ℕ) (fits : lo + size ≤ initial.floor) :
    lo+size ≤ (job).inner.rebased ((job).inner.stageStart addr) := by
  have low : initial.floor ≤ (prior).floor := by
    rw [position_floor (RegisterTimeline.issued (w:=w) traces book) initial (S.length-1)]
    exact DescentDatedAddressBook.floor_mono initial.floor (span _ initial) (Nat.zero_le _)
  have cuts := ((prior).ports.resetPad k).cuts (prior).floor
  have atFloor : initial.floor ≤ addr :=
    (low.trans (cuts.1.trans cuts.2)).trans (((prior).ports.presence k).lower _)
  have booked := (job).inner.occupied ((job).inner.stageStart addr)
  exact fits.trans (((atFloor.trans ((job).inner.ingress.after addr)).trans booked.1).trans booked.2.1)
end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook DescentTerminalFixedSlices
open DescentInitialHost DescentSeedRoot DescentDatedSeedStartup DescentPackedEpochShelves DescentWideSeedFlags
open DescentTerminalEpochChart DescentTerminalEpochDecoder DescentMixedRouter DescentResetInvoice Chronology RegisterTimeline
open DescentPackedProfileInstall DescentExterior DescentExteriorShelf Catalyst CatalystSubstitution CorrectionBatch
open Computability.BorderVNP.Crossing ThreeFlat.Routing
open DescentTerminalCompiledPrefix DescentTerminalPreflightSpace DescentTerminalLocalPortBook
open DescentTerminalLast DescentDatedAddressBook.PhysicalReset ProtocolRAM
open DescentExteriorMatrixUpdate
open DescentTerminalCompiledPrefix.AddressPlan
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 2800000
set_option cleanup.letToHave false
variable {F:Type} [Field F] (G:PoweredGadget F) {n d:ℕ} (board:NonlinearExpanders.Graph n d)
  (op:RotorSpec) (t f g rate cut drift limit τ β h:ℕ) (x:ShellSource F h)
  (branch:G.b≤2^(capRate G t g)) (head dates billed last W slots:ℕ)
local notation "J" => Nat.log 2 h/(2*β)
local notation "tb" => tail τ J
local notation "S" => stageNumbers G t J f g rate x.sites tb
local notation "k" => groupBits t J (hostRate t rate) (capRate G t g) (cutRate t f g)
local notation "p" => headGrain G S k h
local notation "s" => (S).firstWidth G.b p
local notation "W₀" => NativeBranch.binLimit («k»:=k) S
local notation "q" => headArity G S
local notation "w" => W*h
variable (ordinary:OrdinaryRates G (stageNumbers G t (Nat.log 2 h/(2*β)) f g rate x.sites (tail τ (Nat.log 2 h/(2*β)))) (groupBits t (Nat.log 2 h/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) cut) (reset:ResetRates G (stageNumbers G t (Nat.log 2 h/(2*β)) f g rate x.sites (tail τ (Nat.log 2 h/(2*β)))) (groupBits t (Nat.log 2 h/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) (atRound t) n d op.C f g cut (tail τ (Nat.log 2 h/(2*β))))
  (positive:0<(headGrain G (stageNumbers G t (Nat.log 2 h/(2*β)) f g rate x.sites (tail τ (Nat.log 2 h/(2*β)))) (groupBits t (Nat.log 2 h/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) h)) (shorten:reentryRate d op.C*(1-(2-G.rate)/4)^t≤1/2) (fit:(((stageNumbers G t (Nat.log 2 h/(2*β)) f g rate x.sites (tail τ (Nat.log 2 h/(2*β))))).firstWidth G.b (headGrain G (stageNumbers G t (Nat.log 2 h/(2*β)) f g rate x.sites (tail τ (Nat.log 2 h/(2*β)))) (groupBits t (Nat.log 2 h/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) h))<2^(W*h))
  (H degree wire hist:ℕ)
local notation "trace" => traceAt x.X G S ordinary reset branch positive x.opened shorten
local notation "chart" => normalizedPackedChart x.X G S ordinary reset branch positive x.opened shorten w fit
local notation "ss" => (chart).layout
local notation "bins" => terminalBinCount x.X G S p q W₀ n d op.C f g+1
local notation "raw" => terminalRawRows x.X G S p q n d op.C f g
local notation "V" => originalSeedHead G op drift x.X ss S k tb h H degree wire hist bins raw
local notation "origin" => (V).position G op t f g drift h
local notation "lo" => selectorBase x.X (S).copies s h (ss).length
local notation "header" => (V).base G h-1
local notation "menu" => fromProfiles G S board op k tb p f g drift degree h lo header ss
local notation "cursor" => calendar («w»:=w) trace menu origin
local notation "age" => (S).length-1
local notation "phase" => Phase.atPorts G S board k tb age p f g drift degree h (menu).ordinary op
  (cursor age).ports (cursor age).floor
local notation "pitch" => grain (h/2) G.C
local notation "snapshots" => SnapshotCalendar reset (kindCalendar (S).rounds (S).height)
  (capCalendar G.b (S).rounds g (S).height) (snapshotDirectory («w»:=w) trace menu origin)

local notation "z" => originalReplay G board op t f g rate cut drift τ β h x branch W ordinary reset positive
  shorten fit H degree wire hist
local notation "headRate" => t+1+max dates head+2
variable (funds:OriginalWord G board op t f g rate cut drift limit branch head dates billed last W τ β h (drift+1) slots)
  (low:2^h≤x.sites) (dyadic:∃a,x.sites=2^a) (host:x.sites≤H) (upper:H≤hostRows x.sites)
  (coeff:degree≤limit)

local notation "capture" => DescentWideSeedFlags.endInput x.X (S).copies s h+
  DescentPackedSeed.rows x.X (S).copies s h+1
local notation "dates_" => countDates 0 (kindCalendar (S).rounds (S).height)

private def paidArgumentWindow {K : Type} [Field K] (event : Phase K) (first number roof : ℕ) : Prop :=
  first+number ≤ event.dateBase ∧ event.output.metadataEnd event.dateBase ≤ roof

include funds low dyadic host upper coeff in
private theorem original_argument_window :
    paidArgumentWindow phase capture (dates_).length ((z).roleBase G t f g rate β x) := by
  unfold paidArgumentWindow
  have seed := original_funded_seed G board op t f g rate cut drift limit τ β h x branch head dates billed last W slots
    ordinary reset positive shorten fit H degree wire hist funds low dyadic host upper
  have bounds := original_final_event_geometry G board op t f g rate cut drift limit τ β h x branch head dates billed last W slots
    ordinary reset positive shorten fit H degree wire hist funds low dyadic host upper coeff
  constructor
  · exact RegisterTimeline.capture_before_final_reset trace menu origin capture (dates_).length seed.paid
  · exact bounds.2.2.1.le.trans (Nat.le_max_left ..)
end
end Hierarchy.DescentSixParty.SeedNamed

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalGraphPositions DescentTerminalGraphVolume DescentTerminalCableOrder DescentKernelHistory
open DescentBundleHistory DescentPrimitivePalette DescentRotor DescentResetGates CorrectionBatch
open DescentTerminalBinReaddress DescentTerminalPorts Computability.BorderVNP.Crossing
open DescentTerminalEmitter DescentTerminalEmitter.Branch DescentTerminalChipRuntime
open DescentTerminalVertexFields DescentTerminalHeaderScatter DescentTerminalSiteShelves
open DescentTerminalScalarTransposes DescentTerminalDenseWindow DescentTerminalRecipeRows
open DescentTerminalScalarPadded DescentTerminalCompiledPrefix DescentEpochTagKeys
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical BigOperators
open DescentTerminalHost DescentTerminalThreshold DescentTerminalLast DescentTerminalRAM
open DescentTerminalReadout DescentTerminalFixedISAHost CorrectionFrame DescentTerminalChipPins
open ThreeFlat Routing Diagonal TraceBanks
open Computability.VPVNP.RAMMemory TaggedShorterControlHistory Tagged Tagged.SortLift TaggedShorterHistoryOrder
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin Branch.archive Branch.bundleShape SeedNamed.issued normalizedPackedChart

variable {F : Type} [fieldF : Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F)
variable {n h C f g : ℕ} (rounds restart τ β siteCount payloadBits : ℕ)
variable (opened:10*(X.size+1)≤ siteCount) (smaller:siteCount≤(2^payloadBits)^2)
  (low:2^payloadBits≤ siteCount) (dyadic:∃a,siteCount=2^a)
local notation "cut" => cutRate rounds f g
local notation "src_" => (⟨cp,P,siteCount,X,opened,smaller⟩:ShellSource F payloadBits)
local notation "depth_" => Nat.log 2 payloadBits/(2*β)
local notation "tail" => DescentCompiler.TerminalScale.tail τ depth_
local notation "S" => stageNumbers G rounds depth_ f g restart siteCount tail
local notation "k" => groupBits rounds depth_ (hostRate rounds restart) (capRate G rounds g) (cutRate rounds f g)
local notation "W" => NativeBranch.binLimit («k»:=k) S
local notation "j" => Nat.clog 2 (NativeBranch.localLimit G S)
local notation "q" => 2^j*(G.b^(rounds*depth_)*G.b)
local notation "piece" => payloadBits/(16*(q*W))
local notation "rest" => (S).groupWidth k tail 0+k-2*j
local notation "p" => W*piece
variable (ordinary : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch pitch _ => OrdinaryRates G epoch pitch (cutRate rounds f g)))
  (reset : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch pitch frozen => ResetRates G epoch pitch (atRound epoch.rounds) n h C f g (cutRate rounds f g) frozen))
variable (branch : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch _ _ => G.b ≤ 2^epoch.capGain))
  (positive : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch pitch _ => 0 < headGrain G epoch pitch payloadBits))
  (room : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch _ _ => 10*(X.size+1) ≤ epoch.initialSites))
variable (shorten : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch _ _ => reentryRate h C*(1-(2-G.rate)/4)^epoch.rounds ≤ 1/2))
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
local notation "s" => (S).firstWidth G.b p
local notation "Z" => (S).grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "cap" => NativeBranch.privateSlotCapacity G S R
local notation "nodeCap" => (S).epochPower^(S).localTokenExponent
local notation "venues" => (S).groupCount (S).length*2^k

variable (base : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch _ frozen => epoch.baseGroups = 2^frozen))
  (width : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch pitch frozen => epoch.groupWidth pitch frozen 0 + pitch =
      headChunk G epoch + (headChunk G epoch + headRest G epoch pitch frozen)))
variable (age : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch _ _ => 0 < epoch.height))
  (wFit : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch pitch _ =>
      let split := NativeBranch.binLimit («k»:=pitch) epoch
      split ≤ split))
  (qFit : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch _ _ => NativeBranch.localLimit G epoch ≤
      2^(headChunk G epoch)*(G.b^(epoch.rounds*epoch.height)*G.b)))
  (qh : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch _ _ => 0 < 2^(headChunk G epoch)*(G.b^(epoch.rounds*epoch.height)*G.b)))

open DescentExterior Computability.VPVNP.RAMSerialization DescentTerminalExteriorPackets DescentTerminalPublicIdentity
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall DescentPackedProfileTape
open DescentSeedRoot DescentExteriorShelf DescentTerminalPrimitiveArena
local notation "E₀" => Fintype.card (Port P X.width)
local notation "H₀" => (S).hostSize (S).length
local notation "count₀" => E₀*2^(j+rest)
variable (sitesPositive : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch _ _ => 0 < epoch.hostSize epoch.length))
local notation "sitePos_" => ((Nat.two_pow_pos payloadBits).trans_le low)
local notation "template" => shellTemplate X G rounds depth_ f g restart siteCount τ payloadBits n h C sitePos_
local notation "rawWords" => terminalRawRows X G S p q n h C f g
local notation "headerRows" => terminalPool X G S p q W n h C f g
local notation "paidRows" => headerRows
local notation "cfg" => Branch.exteriorShape template E₀ j rest s rawWords headerRows H₀ sitesPositive
local notation "shape_" => original_shell_fields X G rounds depth_ f g restart siteCount τ payloadBits n h C sitePos_
local notation "pool" => (shape_).1
local notation "raw" => (shape_).2.1
open DescentTerminalCompiledPrefix.AddressPlan DescentTerminalEmitter.Compact
open DescentTerminalLocalPortBook DescentTerminalSpanBook DescentTerminalBinPack
open DescentTerminalPreflightSpace ThreeFlat.RAM PhysicalProcedure

open DescentPackedEpochFold DescentExteriorMatrixUpdate DescentPackedSeed DescentSeedRoot
open ThreeFlat Routing Diagonal
variable (ratio₀:ℕ)
local notation "w" => ratio₀*payloadBits
variable (fit : AtPurchasedStage G rounds f g restart τ β siteCount payloadBits
    (fun epoch pitch _ => epoch.firstWidth G.b (headGrain G epoch pitch payloadBits) < 2^(ratio₀*payloadBits)))
local notation "K" => calibratedBins X G rounds depth_ f g restart siteCount τ payloadBits n h C
local notation "chart" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
local notation "fmt" => Branch.geometryFormat G S k g p tail q R rot headerRows paidRows
local notation "pre" => Branch.preflightSpec X G S k g p tail ({fmt with binSize:=W}:Branch.PreflightFormat)
local notation "steps" => (chart).layout
local notation "lo" => DescentWideSeedFlags.selectorBase X (S).copies s payloadBits (steps).length
local notation "packWidth" => DescentPackedEpochShelves.grain (payloadBits/2) G.C
local notation "matrixAt" => end_ (lo+extent packWidth steps) G.C packWidth
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentResetInvoice CorrectionBatch
open DescentSixParty.SeedNamed.Branch DescentExteriorReplay DescentTerminalFixedSlices
open DescentTerminalPointerDigits DescentTerminalCombinedRole DescentSIMDLookup DescentPackedColony
open ThreeFlat.Routing CallPool DescentColonies DescentActorRaster DescentColonies.SplitRAM
open DescentTerminalRoleTables DescentTerminalPointerIssue
open Chronology DescentDatedSeedStartup.Input DescentTerminalEpochDecoder
variable (headRate_ datesRate_ codeRate_ lastRate_ slots_:ℕ)
local notation "dateDegree" => maximumDegree (rounds+1)
local notation "board" => reset.board
local notation "bootHosts" => siteCount
local notation "seedWire_" => (S).epochPower^(S).priceExponent
local notation "seedHist_" => s
local notation "vhead_" => originalSeedHead G rot R X steps S k tail payloadBits bootHosts dateDegree seedWire_ seedHist_
  (terminalBinCount X G S p q W n h C f g+1) rawWords
local notation "startup" => (vhead_).layout G rounds f g R payloadBits
local notation "startingHeader" => (vhead_).base G payloadBits-1
variable (funding :
  let historySize := max 1 (max reset.bitsR (C*reset.bitsR))
  OriginalWord G reset.board (RotorSpec.ofRates reset) rounds f g restart (cutRate rounds f g)
    historySize (maximumDegree (rounds+1)) branch headRate_ datesRate_ codeRate_ lastRate_
    ratio₀ τ β payloadBits (historySize+1) slots_)
local notation "heads_" => original_funded_seed G board rot rounds f g restart cut R dateDegree τ β payloadBits src_ branch
  headRate_ datesRate_ codeRate_ lastRate_ ratio₀ slots_ ordinary reset positive shorten fit siteCount
  dateDegree seedWire_ seedHist_ funding low dyadic le_rfl (Nat.le_pow_clog (by decide : 1<2) siteCount)
local notation "hostsEnough" => (heads_).hosts
local notation "primitiveLanes_" => DescentDatedSeedStartup.Primitive.paletteLanes G rot (startup).seedWidth Z payloadBits k
local notation "seedEnd_" => (DescentDatedSeedStartup.Input.nodeChart startup k bootHosts ((S).groupCount 0)).seedEnd
  (DescentDatedSeedStartup.endAddress X startup bootHosts ((S).groupCount 0) k)
local notation "initialBound_" => DescentDatedSeedStartup.Primitive.initialEnd X (S).copies (startup).seedWidth payloadBits k
  bootHosts ((S).groupCount 0) primitiveLanes_ seedEnd_

local notation "entry_" => (⟨DatePorts.initial G rot X (S).copies startup k bootHosts ((S).groupCount 0) payloadBits Z,
    initialBound_⟩ : RegisterTimeline.Position)
local notation "traces_" => traceAt X G S ordinary reset branch positive room shorten
local notation "menu_" => RegisterTimeline.fromProfiles G S board rot k tail p f g R dateDegree payloadBits lo startingHeader steps
local notation "cursor_" => RegisterTimeline.calendar («w»:=w) traces_ menu_ entry_
local notation "datesAt" => RunTrace.machine traces_ (fun i _=>RegisterTimeline.instruction («w»:=w) traces_ menu_ entry_ i)
local notation "dateAge" => (S).length-1
local notation "prior_" => cursor_ dateAge
local notation "ordinaryAt" => (menu_).ordinary
local notation "datePayload" => payloadBits
local notation "operandLanes" => (prior_).ports.operandLanes
local notation "primitiveLanes" => (prior_).ports.roleLanes
local notation "previousDate" => (prior_).ports.venue
local notation "priorAddress" => (prior_).ports.io.wire
local notation "rosterBank" => (prior_).ports.io.roster
local notation "datedFloor" => (prior_).ports.priorStart k (prior_).floor
local notation "dateTag" => RegisterTimeline.Menu.resetFlag S
local notation "dateRotation" => fun i=>(menu_).rotationAt G S k i (cursor_ i)
local notation "countAt" => fun i=>(menu_).selectorAt G S k i (cursor_ i)
local notation "rankDir_" => RegisterTimeline.snapshotDirectory («w»:=w) traces_ menu_ entry_
local notation "snapshots" => SnapshotCalendar reset (kindCalendar (S).rounds (S).height)
  (capCalendar G.b (S).rounds g (S).height) rankDir_
local notation "rankFloor" => (cursor_ (S).length).floor
local notation "roleBase" => max rankFloor (matrixAt+32*DescentExteriorShelf.span j rest s E₀)
local notation "replayBase" => roleBase+DescentTerminalRoleTables.count (originalRoleBits G rot S p R)

local notation "dateSpec" => preflightSpec X G S k g p tail (geometryFormat G S k g p tail q R rot headerRows paidRows)
local notation "datePorts" => Fintype.card (Port P X.width)
local notation "datePhase" => Phase.scheduled G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
  operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
local notation "dateOut" => (datePhase).output
local notation "dateOrigin" => (datePhase).dateBase
local notation "dateMachine" => PhysicalReset.scheduled G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
  s Z operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
local notation "dateCalendar" => replayCalendar X S k tail j rest snapshots
local notation "earlyFloor" => DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail replayBase j rest s datePorts
local notation "earlyImage" => DescentExteriorMatrixUpdate.Calendar.earlyImage S k tail replayBase dateTag dateRotation j rest s datePorts matrixAt
local notation "sliceEnd" => (datePhase).stop earlyFloor
local notation "lookupBase" => (dateCalendar).packetEnd sliceEnd
local notation "lookupPage" => (dateSpec).scanPages lookupBase q
local notation "censusBase" => (lookupPage).stop
local notation "dateHardware" => (dateOut).receiver
local notation "dateBlocks" => (dateSpec).scalar.blocks
local notation "blockCast" => (rfl : dateBlocks=(dateHardware).blocks)
local notation "paidBank" => fun x:Fin dateBlocks=>(dateOut).terminalPaid dateOrigin x.val
local notation "actorBank" => fun x:Fin dateBlocks=>(dateOut).terminalActor dateOrigin x.val
local notation "wingBank" => fun (x:Fin dateBlocks) (a:Fin (2*(dateSpec).cap))=>(dateOut).terminalWing dateOrigin x.val a.val
local notation "peerBank" => (dateOut).terminalPeer dateOrigin
local notation "dateColors" => DescentPrimitivePalette.colors G s Z rot
local notation "roleBankBits" => fun roleField:Fin 6=>DescentTerminalCombinedRole.width dateColors (max 8 (2^(S).capGain))
  cap p R roleField*((S).epochPower^(S).localTokenExponent)*(dateSpec).groups
local notation "atomBits" => Nat.clog 2 (nodeCap+1)
local notation "operandWidths" => (⟨atomBits,Nat.clog 2 (cap+1),fun _=>DescentOperandWidth.recordBits G S k tail R 3 p,some nodeCap⟩:Widths)
local notation "terminalPin" => DescentExterior.terminalPin ((S).groupWidth k tail 0+k) ((S).groupWidth k tail (S).length+k) (k*(S).length)
local notation "publicCell" => DescentTerminalPointerDigits.publicCell («cap»:=(dateSpec).cap) (N:=nodeCap) (A:=cap)
  (d:=(dateSpec).scalar.pointerBits) 3 q G.b (poolBatchCount (s*1) p) (k*(S).length) (dateSpec).groups operandWidths
local notation "privateCell" => DescentTerminalPointerDigits.output (dateSpec).cap nodeCap cap 3 (dateSpec).groups
  (dateSpec).scalar.pointerBits (Nat.clog 2 (q+cap+1)) q G.b (poolBatchCount (s*1) p) operandWidths terminalPin
local notation "roleBanks" => DescentTerminalRoleTables.role roleBankBits ((datePhase).banks earlyFloor) roleBase
local notation "arityBanks" => DescentTerminalRoleTables.arity roleBankBits ((datePhase).banks earlyFloor) roleBase
local notation "matrixFloor" => DescentExteriorMatrixUpdate.Calendar.stop S k tail replayBase+(S).length
local notation "pointerBank" => fun (pointerField:Fin 4) (slot:Fin (dateOut).argumentSlots) (block:Fin dateBlocks) =>
  (dateOut).terminalPointers dateOrigin pointerField slot (block.cast blockCast)
local notation "oldOperands" => DescentTerminalOperandRepack.padded («K»:=cap) pointerBank paidBank
local notation "operandChart" => ((dateSpec).pointerPages censusBase matrixFloor oldOperands wingBank).address (N:=nodeCap)
local notation "replayRoom" => purchased_census_replay_room X G rounds restart τ β siteCount payloadBits
  opened smaller low dyadic ordinary reset branch positive room shorten ratio₀ fit headRate_ datesRate_
  codeRate_ lastRate_ slots_ funding
local notation "dateEntryAt" mu => (dateCalendar).memory sliceEnd censusBase replayRoom ((datePhase).memory earlyFloor (earlyImage mu))
local notation "primitiveOf" mu => (dateSpec).primitiveSnapshot (base:=censusBase) («w»:=w) («q»:=q) («p»:=p) (nd:=atomBits)
  (nodes:=nodeCap) (hidden:=cap) (args:=cap) (oldPaid:=paidBank) (actor:=actorBank) (first:=roleBanks) (second:=arityBanks)
  («chart»:=operandChart) (f0:=publicCell) (f7:=privateCell) ((lookupPage).image (dateEntryAt mu))
local notation "datedDecoder" => Branch.decodeBook S G base ordinary.radix p q 3
  (dateSpec).cap (dateSpec).printBits (by decide)
local notation "booksOf" mu => (dateSpec).bookSnapshot (base:=censusBase) («peer»:=peerBank) (wing:=wingBank)
  («w»:=w) («q»:=q) («p»:=p) (nd:=atomBits) (nodes:=nodeCap) (hidden:=cap) (args:=cap)
  (oldPaid:=paidBank) (actor:=actorBank) (first:=roleBanks) (second:=arityBanks) («chart»:=operandChart)
  (f0:=publicCell) (f7:=privateCell) (decode:=datedDecoder) ((lookupPage).image (dateEntryAt mu))
local notation "dateHomes" => (dateCalendar).homes sliceEnd

local notation "begin_" => censusBase
local notation "peer" => peerBank
local notation "old" => wingBank
local notation "org" => lookupBase
local notation "homes" => dateHomes
local notation "arity" => max 8 (2^(S).capGain)
local notation "groups" => cap
local notation "stride" => R
local notation "oldTags" => DescentPrimitivePalette.colors G s Z rot
local notation "tagCount" => DescentBundleTagKeys.capacity oldTags arity groups p stride
local notation "pages₀" => (pre).scanPages org q
local notation "total" => (pages₀).total
local notation "grain" => p
local notation "codes" => DescentTerminalScalarHeader.range q tagCount cap nodeCap cap p venues
local notation "seed" => (chart).seed
local notation "clockCap" => G.C
local notation "front" => end_ (lo+extent packWidth steps) clockCap packWidth+17*DescentExteriorShelf.span j rest s E₀
local notation "extra" => DescentTerminalPublicIdentity.total K W q piece codes rawWords count₀
local notation "Full" => DescentTerminalFullPins.Candidate ((chart).Pin⊕Hidden E₀ j rest s) K W q piece rawWords
local notation "power" => NativeBranch.copy_power S (radix:=ordinary.radix) base width
local notation "compact" => end_ (lo+extent packWidth steps) G.C packWidth
local notation "seedBase" => DescentWideSeedFlags.endInput X (S).copies s payloadBits
local notation "seedRows" => DescentPackedSeed.rows X (S).copies s payloadBits
open Chronology DescentDatedSeedStartup.Input DescentTerminalEpochDecoder DescentPackedSeed DescentExteriorShelf
local notation "capture" => seedBase+seedRows+1
local notation "replayFits" => purchased_role_replay_fits X G rounds restart τ β siteCount payloadBits
  opened smaller low dyadic ordinary reset branch positive room shorten ratio₀ fit headRate_ datesRate_
  codeRate_ lastRate_ slots_ funding
local notation "roleMount" => originalRoleMount G rot S p R roleBase replayBase le_rfl replayFits
local notation "captureDates" => countDates 0 (kindCalendar (S).rounds (S).height)
local notation "rowAddress" => fun i:ℕ=>countAt ((captureDates)[i]?.getD 0)
local notation "countSlot" => fun i:ℕ=>capture+i
local notation "count" => countSlot
local notation "extPins" => Port (((S).copies*s)*P) (copiesWidth ((S).copies*s) X.width)
local notation "view" x₀ => Branch.copyInput X s power x₀
local notation "bootFor" x₀:arg z₀:arg => Root.appended front extra
    (Root.widePackedImage X (S).copies s payloadBits w seed lo G.C packWidth steps compact
      (DescentExterior.publicRows X (view x₀)) (Sum.elim (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inl)
      (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inr)))
    (DescentTerminalPublicIdentity.back (z₀ ∘ DescentTerminalFullPins.chip) w codes count₀)

local notation "histAt" z₀ => (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inl)
local notation "checkedAt" x₀:arg z₀:arg => DescentWideSeedFlags.countedAt X (S).copies s payloadBits seed
  (histAt z₀) (bootFor x₀ z₀)
local notation "startedAt" x₀:arg z₀:arg => completeImage G rot X ((S).initialDigits ordinary.radix) hostsEnough startup
  startingHeader payloadBits Z (checkedAt x₀ z₀)
local notation "lastAt" x₀:arg z₀:arg => DateCode.history datesAt (startedAt x₀ z₀) (S).length
local notation "capturedAt" x₀:arg z₀:arg => (roleMount).phase.image (DescentLowCountBook.output capture rowAddress (lastAt x₀ z₀) (captureDates).length)
local notation "primitiveBank" => fun (x₀:extPins→Bool)(z₀:Full→Bool)=>primitiveOf (capturedAt x₀ z₀)
local notation "booksBank" => fun (x₀:extPins→Bool)(z₀:Full→Bool)=>booksOf (capturedAt x₀ z₀)
local notation "B" => (pre).pageBits
local notation "candidatePrior" => wideChoicePrior X G S ordinary reset branch positive room shorten w fit base width
local notation "matrixAtSource" x₀:arg z₀:arg c₀:arg => primitiveBank x₀ z₀ matrixFloor =
  ((DescentExterior.matrixCode (Branch.pinSpine X G S (issued X G S ordinary reset branch positive room shorten c₀)
    positive base).matrix).val:Computability.VPVNP.BurstRAM.Word w)
local notation "paidPacketsAt" x₀:arg z₀:arg c₀:arg => WideMeasuredPackets (X:=X) (G:=G) («S»:=S) (ordinary:=ordinary)
  (reset:=reset) (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (c:=c₀)
  (base:=base) (width:=width) («headerRows»:=headerRows) («paidRows»:=paidRows)
  («begin_»:=censusBase) («peer»:=peerBank) («old»:=wingBank) («org»:=lookupBase) («homes»:=dateHomes)
  (primitive:=primitiveBank x₀ z₀) (m:=booksBank x₀ z₀)
private abbrev paidRegisteredDate := @WideRegisteredDateRows

local notation "registeredAtHeap" c₀:arg mu:arg din:arg => @paidRegisteredDate
  F fieldF cp P X G S k cut tail n h C f g
  W q piece ordinary reset branch positive room shorten c₀ j rest headerRows paidRows w h
  board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixAt
  dateRotation snapshots roleBase mu din

local notation "registeredAt" x₀:arg z₀:arg c₀:arg din:arg =>
  registeredAtHeap c₀ (show Memory w from capturedAt x₀ z₀) din

local notation "fundedReel" => originalReplay G board rot rounds f g restart cut R τ β payloadBits src_
  branch ratio₀ ordinary reset positive shorten fit siteCount dateDegree seedWire_ seedHist_


local notation "paidOrigin" => (vhead_).position G rot rounds f g R payloadBits
local notation "sourcePrior" => RegisterTimeline.calendar («w»:=w) traces_ menu_ paidOrigin dateAge
local notation "fundedPhase" => Phase.atPorts G S board k tail dateAge p f g R dateDegree payloadBits ordinaryAt rot
  (sourcePrior).ports (sourcePrior).floor
local notation "thisPhase" => Phase.scheduled G S board k tail dateAge p f g R dateDegree payloadBits ordinaryAt rot
  operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
local notation "captureFirst" => DescentWideSeedFlags.endInput X (S).copies s payloadBits +
  DescentPackedSeed.rows X (S).copies s payloadBits + 1



include opened smaller in
private theorem paidArgumentRoleBase : (fundedReel).roleBase G rounds f g restart β src_ = roleBase := by
  unfold CensusReplay.roleBase Hierarchy.DescentSixParty.SeedNamed.replayBase
  dsimp only [originalReplay]
  rfl

set_option maxHeartbeats 1800000 in
private theorem paidArgumentPhase : fundedPhase = thisPhase := rfl

include funding opened smaller low dyadic in
set_option maxHeartbeats 2800000 in
private theorem purchasedArgumentWindow :
    paidArgumentWindow fundedPhase captureFirst (captureDates).length ((fundedReel).roleBase G rounds f g restart β src_) :=
  original_argument_window G board rot rounds f g restart cut R dateDegree τ β payloadBits src_ branch headRate_ datesRate_
    codeRate_ lastRate_ ratio₀ slots_ ordinary reset positive shorten fit siteCount dateDegree seedWire_ seedHist_
    funding low dyadic le_rfl (Nat.le_pow_clog (by decide : 1 < 2) siteCount) le_rfl

private theorem paidArgumentWindow_transfer {kField : Type} [Field kField]
    {left right : Phase kField} {front₀ numCells floorA floorB : ℕ} (event : left = right)
    (roof : floorA = floorB) (from_ : paidArgumentWindow left front₀ numCells floorA) :
    paidArgumentWindow right front₀ numCells floorB := by cases event; cases roof; exact from_

include funding opened smaller low dyadic in
set_option maxHeartbeats 2800000 in
private theorem paidActualArgumentWindow :
    paidArgumentWindow thisPhase captureFirst (captureDates).length roleBase := by
  have eqDate := paidArgumentPhase (X:=X) (G:=G) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
    (shorten:=shorten) (fit:=fit)
  have eqRoof := paidArgumentRoleBase (X:=X) (G:=G) (opened:=opened) (smaller:=smaller)
    (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (fit:=fit)
  have bought := purchasedArgumentWindow (X:=X) (G:=G) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (funding:=funding)
    (opened:=opened) (smaller:=smaller) (low:=low) (dyadic:=dyadic) (fit:=fit) (shorten:=shorten) (room:=room)
  exact paidArgumentWindow_transfer eqDate eqRoof bought


private structure PurchasedWordTypes where
  roleProperty : Prop
  arityProperty : Prop
  operandProperty : Prop
  completeProperty : Prop
  fromParts : roleProperty → arityProperty → operandProperty → completeProperty

private theorem PurchasedWordTypes.assemble (t : PurchasedWordTypes)
    (headers : t.roleProperty ∧ t.arityProperty)
    (operands : t.arityProperty → t.operandProperty) : t.completeProperty :=
  t.fromParts headers.1 headers.2 (operands headers.2)

open Lean Elab Term Meta in
local elab "purchasedWordFields% " "["args:term,*"]" : term => do
  let values ← args.getElems.mapM fun arg => do
    elabTerm arg none
  let constructor := Lean.mkConst ``OriginalSiteWords.mk
  let beforeRoom ← instantiateForall (← inferType constructor) values
  let .forallE name roomType _ _ := beforeRoom | throwError "Expected the late replay room"
  withLocalDeclD name roomType fun rm => do
    let completeArgs := values.push rm
    let type ← instantiateForall beforeRoom #[rm]
    let .forallE _ roles (.forallE _ arities (.forallE _ operands _ _) _) _ := type
      | throwError "Expected the three original site word fields"
    let complete := mkAppN (Lean.mkConst ``OriginalSiteWords) completeArgs
    let packed := mkAppN (Lean.mkConst ``PurchasedWordTypes.mk)
      #[roles, arities, operands, complete, mkAppN constructor completeArgs]
    mkLambdaFVars #[rm] packed

set_option maxHeartbeats 4800000 in
private def purchasedOriginalWordTypes
    (c₀:(last).Choice) (mu:Memory w) :=
  purchasedWordFields% [F, fieldF, cp, P, X, G, S, k, cut, tail, n, h, C, f, g,
    W, q, piece, ordinary, reset, branch, positive, room, shorten, c₀, j, rest, base, width, age,
    wFit, qFit, qh, template, sitesPositive, rawWords, headerRows, paidRows, pool, raw, w, h, board,
    dateAge, dateDegree, datePayload, ordinaryAt, operandLanes, primitiveLanes, previousDate,
    priorAddress, rosterBank, datedFloor, replayBase, matrixAt, dateTag, (show ℕ → ℕ from dateRotation),
    snapshots, roleBase, mu]

local notation "paidSiteFields" x₀:arg z₀:arg c₀:arg =>
  @purchasedOriginalWordTypes F fieldF cp P X G n h C f g rounds restart τ β siteCount payloadBits
    low ordinary reset branch positive room shorten base width age wFit qFit qh sitesPositive ratio₀ fit
    c₀ (capturedAt x₀ z₀) replayRoom

open Lean Elab Term in
local elab "ballotApply% " fn:term:arg "[" args:term,* "]" : term => do
  return mkAppN (← elabTerm fn none) (← args.getElems.mapM fun arg => elabTerm arg none)



set_option maxHeartbeats 4800000 in
set_option maxRecDepth 12000 in
set_option cleanup.letToHave false in
private def fundedOriginalBallotWordTypes (x₀:extPins→Bool) (z₀:Full→Bool) (c₀:(last).Choice) :=
  ballotApply% @purchasedOriginalWordTypes [F,fieldF,cp,P,X,G,n,h,C,f,g,rounds,restart,τ,β,siteCount,
    payloadBits,low,ordinary,reset,branch,positive,room,shorten,base,width,age,wFit,qFit,qh,sitesPositive,
    ratio₀,fit,c₀,(show Memory w from capturedAt x₀ z₀),replayRoom]


open Lean Meta Elab Command

private def capturedFieldAt (xs : Array Lean.Expr) (i : Nat) : MetaM Lean.Expr := do
  let some x := xs[i]? | throwError "Missing input at index {i} of {xs.size}"
  return x

private def capturedStageParameter (xs : Array Lean.Expr) (fieldName : Name) : MetaM Lean.Expr := do
  let some x ← xs.findM? (fun x => do return (← x.fvarId!.getDecl).userName.eraseMacroScopes == fieldName) | throwError "Missing actual funding parameter {fieldName}"
  return x

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.modifyState env ("paidCapturedRoleFields" :: "purchased_site_roles_arities" :: ·)

set_option maxHeartbeats 5200000 in
set_option maxRecDepth 16000 in
set_option cleanup.letToHave false in
run_cmd liftTermElabM do
  let schema ← getConstInfo ``fundedOriginalBallotWordTypes
  let role ← getConstInfo ``final_site_roles_arities_at_height
  let registered ← getConstInfo ``WideRegisteredDateRows
  let shell ← getConstInfo ``original_shell_short
  forallTelescope schema.type fun xs _ => do
    let applied := (schema.value!.beta xs).consumeMData
    unless applied.getAppFn.constName? == some ``purchasedOriginalWordTypes do throwError "Unrecognized actual paid field bundle {applied.getAppFn.constName?}"
    let package ← getConstInfo ``purchasedOriginalWordTypes
    let packed := (package.value!.beta applied.getAppArgs).headBeta.consumeMData
    unless packed.getAppFn.constName? == some ``PurchasedWordTypes.mk do throwError "Expected original word field constructor {packed.getAppFn.constName?}"
    let words := (← capturedFieldAt packed.getAppArgs 3).consumeMData
    unless words.getAppFn.constName? == some ``OriginalSiteWords do throwError "Expected the original ballot's 61 constructor fields"
    let ws := words.getAppArgs
    unless ws.size == 61 do throwError "Wrong number of paid fields: {ws.size}"
    let args := ws.extract 0 60
    let heap := args[59]!.consumeMData
    let some mount := heap.find? (fun e => e.isAppOfArity ``originalRoleMount 12) | throwError "Cannot identify actual captured role mount in {heap.getAppFn.constName?}"
    let ma := mount.getAppArgs
    unless ma.size == 12 do throwError "Missing role bank fields"
    let budget ← capturedStageParameter xs `payloadBits
    let sched := ws[6]!.getAppArgs
    unless sched.size >= 7 do throwError "Expected actual purchased stage schedule {ws[6]!.getAppFn.constName?}"
    let shellArgs := #[ws[0]!,ws[1]!,ws[2]!,ws[3]!,ws[4]!,ws[5]!,←capturedStageParameter xs `rounds,sched[sched.size-6]!,ws[13]!,ws[14]!,←capturedStageParameter xs `restart,←capturedStageParameter xs `siteCount,←capturedStageParameter xs `τ,budget,ws[10]!,ws[11]!,ws[12]!,ma[3]!,ma[6]!]
    let sizeProof := mkAppN (mkConst shell.name) shellArgs
    let baseRole := mkAppN (mkConst role.name) args
    let roleType ← instantiateForall role.type args
    let .forallE `dateInput inTy _ _ := roleType | throwError "original role theorem lost its paid date input"
    withLocalDeclD `din inTy fun din => withLocalDeclD `restored inTy fun restored => do
      let regs := (args.extract 0 27) ++ #[ws[36]!,ws[37]!] ++ (ws.extract 40 55) ++ (ws.extract 56 60) ++ #[din]
      unless regs.size == 49 do throwError "Expected 49 actual registered date parameters"
      let physical := (registered.value!.beta regs).consumeMData
      unless physical.getAppFn.constName? == some ``PrimitiveDateRows do throwError "Registered date failed to expose the original physical row"
      let some actualRoster := physical.getAppArgs.back? | throwError "Empty original physical date application"
      let operands := #[din,ws[60]!,restored,budget,actualRoster]
      let registeredType := mkAppN (mkConst registered.name) regs
      withLocalDeclD `date registeredType fun date => do
        let supplied := operands ++ #[date,sizeProof]
        let t ← instantiateForall roleType supplied
        let .forallE `scalar scalarTy _ _ := t | throwError "Expected the independent scalar budget"
        withLocalDeclD `scalar scalarTy fun scalar => do
          let some copied := heap.find? (fun e => e.isAppOfArity ``DescentLowCountBook.output 5) | throwError "Cannot find the actual low-count copy in the mounted ballot"
          let paid := #[scalar,ma.back!,copied]
          let mt ← instantiateForall t paid
          let .forallE `mounted mountEq _ _ := mt | throwError "Missing mounted word equality"
          let some (_,lhs,_) := mountEq.eq? | throwError "Expected physical image equality"
          let witness ← mkEqRefl lhs
          let out := mkAppN baseRole (supplied ++ paid ++ #[witness])
          let ends ← instantiateForall mt #[witness]
          unless ends.isForall do throwError "Expected the actual archive fields"
          let all := xs ++ #[din,restored,date,scalar]
          let ty ← mkForallFVars all ends
          let val ← mkLambdaFVars all out
          addDecl (.thmDecl {name := mkPrivateName (← getEnv) `OAI.Hierarchy.DescentSixParty.SeedNamed.paidCapturedRoleFields, levelParams := schema.levelParams, type := ty, value := val})

open Lean Meta Elab Command

/- Fix all the indices of the funded original image before joining its three reads. -/
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4800000 in
set_option cleanup.letToHave false in
run_cmd liftTermElabM do
  let schema ← getConstInfo ``fundedOriginalBallotWordTypes
  forallTelescope schema.type fun xs _ => do
    let supplied := (schema.value!.beta xs).consumeMData
    unless supplied.getAppFn.constName? == some ``purchasedOriginalWordTypes do
      throwError "The paid ballot must supply the original site indices"
    let pack ← getConstInfo ``purchasedOriginalWordTypes
    let shape := (pack.value!.beta supplied.getAppArgs).headBeta.consumeMData
    unless shape.isAppOfArity ``PurchasedWordTypes.mk 5 do throwError "Expected the five original site field constructors"
    let parts := shape.getAppArgs
    let original := parts[3]!.consumeMData
    unless original.isAppOfArity ``OriginalSiteWords 61 do throwError "Expected the 61 measured site fields"
    let headersTy := mkApp2 (Lean.mkConst ``And) parts[0]! parts[1]!
    let operandsTy ← mkArrow parts[1]! parts[2]!
    withLocalDeclD `headers headersTy fun headers => withLocalDeclD `operands operandsTy fun operands => do
      let decodedRoleProof := mkAppN (Lean.mkConst ``And.left) #[parts[0]!,parts[1]!,headers]
      let decodedArityProof := mkAppN (Lean.mkConst ``And.right) #[parts[0]!,parts[1]!,headers]
      let assembled := mkAppN parts[4]! #[decodedRoleProof,decodedArityProof,mkApp operands decodedArityProof]
      let binders := xs ++ #[headers,operands]
      let statement ← mkForallFVars binders original
      let witness ← mkLambdaFVars binders assembled
      addDecl (.thmDecl {
        name := mkPrivateName (← getEnv) `OAI.Hierarchy.DescentSixParty.SeedNamed.fundedSiteWordsAtCapturedMemory
        levelParams := schema.levelParams, type := statement, value := witness})

open Lean Meta Elab Term

private def roleFundingLocal (binder : Name) (bi : BinderInfo := .default) : MetaM Lean.Expr := do
  let c ← getLCtx
  if let some d := c.findFromUserName? binder then return d.toExpr
  for d in c do
    if d.userName.eraseMacroScopes == binder.eraseMacroScopes || (bi.isInstImplicit && d.binderInfo.isInstImplicit) then return d.toExpr
  throwError "Missing original funding binder {binder}"

private partial def roleFundingArgs (ty : Lean.Expr) (mount : Option Lean.Expr := none) : MetaM (Array Lean.Expr) := do
  let mut args := #[]
  let mut t := ty
  while t.isForall do
    let .forallE n _ argumentBody bi := t | unreachable!
    let x ← if n == `mount && mount.isSome then pure mount.get! else roleFundingLocal n bi
    args := args.push x
    t := argumentBody
  return args

private def printedCapturedRoleProof (fundedArgs : Array Lean.Expr)
    (din date scalar restored printed printedType goal : Lean.Expr) : MetaM Lean.Expr := do
  let stamped := printedType.consumeMData
  unless stamped.isAppOf ``FinalPrintedArchive do
    throwError "Expected the mounted FinalPrintedArchive at the restored date"
  let archive ← getConstInfo ``FinalPrintedArchive
  let archiveBody := archive.instantiateValueLevelParams! stamped.getAppFn.constLevels!
  let layoutExists := (archiveBody.beta stamped.getAppArgs).headBeta.consumeMData
  unless layoutExists.isAppOfArity ``Exists 2 do
    throwError "FinalPrintedArchive must supply its original range room"
  let layoutArgs := layoutExists.getAppArgs
  let consumeLayout ← withLocalDeclD `places layoutArgs[0]! fun places => do
    let flagsExists := (layoutArgs[1]!.beta #[places]).headBeta.consumeMData
    unless flagsExists.isAppOfArity ``Exists 2 do
      throwError "The printed range room must contain its flag rows"
    let flagsArgs := flagsExists.getAppArgs
    withLocalDeclD `recorded flagsExists fun recorded => do
      let consumeFlags ← withLocalDeclD `flags flagsArgs[0]! fun flags => do
        let readType := (flagsArgs[1]!.beta #[flags]).headBeta.consumeMData
        let wordParts := readType.getAppArgs
        unless readType.isAppOf ``DatePorts.ArchiveRead && wordParts.size >= 3 do
          throwError "Expected an ArchiveRead containing the physical pointer and flag rows"
        withLocalDeclD `printedRead readType fun printedRead => do
          let ptr := wordParts[wordParts.size - 3]!
          let recordedFlags := wordParts[wordParts.size - 2]!
          let reader ← getConstInfo ``paidCapturedRoleFields
          let roleProof := mkAppN (Lean.mkConst reader.name)
            (fundedArgs ++ #[din, restored, date, scalar, places, ptr, recordedFlags, printedRead])
          mkLambdaFVars #[flags, printedRead] roleProof
      let useFlags := mkAppN (Lean.mkConst ``Exists.elim flagsExists.getAppFn.constLevels!)
        #[flagsArgs[0]!, flagsArgs[1]!, goal, recorded, consumeFlags]
      mkLambdaFVars #[places, recorded] useFlags
  return mkAppN (Lean.mkConst ``Exists.elim layoutExists.getAppFn.constLevels!)
    #[layoutArgs[0]!, layoutArgs[1]!, goal, printed, consumeLayout]

private def roleArchiveFromConcreteFunding (goal : Lean.Expr) : MetaM Lean.Expr := do
  let schema ← getConstInfo ``fundedOriginalBallotWordTypes
  let xs ← roleFundingArgs schema.type
  let application := (schema.value!.beta xs).consumeMData
  let words ← getConstInfo application.getAppFn.constName!
  let wordParts := (words.value!.beta application.getAppArgs).headBeta.consumeMData
  let packed := wordParts.getAppArgs[3]!
  unless packed.getAppFn.constName? == some ``OriginalSiteWords && packed.getAppNumArgs == 61 do
    throwError "Expected the stored 61 original word wordParts"
  let heap := packed.getAppArgs[59]!
  let some actualMount := heap.find? (fun e => e.isAppOfArity ``originalRoleMount 12)
    | throwError "The purchased original memory must use the registered mount"
  let donor ← getConstInfo ``purchased_final_role_archive
  let args ← roleFundingArgs donor.type actualMount
  let mounted := mkAppN (Lean.mkConst donor.name) args
  let ret := (← instantiateForall donor.type args).consumeMData
  let params := ret.getAppArgs
  unless params.size == 19 && params[14]! == actualMount do throwError "Expected the actual purchased terminal mount"
  let conversion ← getConstInfo ``restoreRoleArchiveInput
  let rawRows := params[17]!.consumeMData
  let rowsDef ← getConstInfo rawRows.getAppFn.constName!
  let rows := (rowsDef.value!.beta rawRows.getAppArgs).headBeta
  let payload := (params.set! 17 rows).push mounted
  let bought := mkAppN (Lean.mkConst conversion.name) payload
  let existsT := (← instantiateForall conversion.type payload).consumeMData
  unless existsT.isAppOfArity ``Exists 2 do throwError "The archive must purchase a restored physical input"
  let ex := existsT.getAppArgs
  let din ← roleFundingLocal `din
  let date ← roleFundingLocal `date
  let scalar ← roleFundingLocal `scalarRoom
  let claim ← withLocalDeclD `restored ex[0]! fun restored => do
    let printedT := (ex[1]!.beta #[restored]).consumeMData
    withLocalDeclD `printed printedT fun printed => do
      let body ← printedCapturedRoleProof xs din date scalar restored printed printedT goal
      mkLambdaFVars #[restored,printed] body
  return mkAppN (Lean.mkConst ``Exists.elim existsT.getAppFn.constLevels!) #[ex[0]!,ex[1]!,goal,bought,claim]

open Lean Meta Elab Command
private partial def paidRoleSupplyArchive {α : Type} [Inhabited α] (ty : Lean.Expr)
    (finish : MetaM α) : MetaM α := do
  let .forallE paidRoleBinderName paidRoleBinderDomain paidRoleBinderBody paidRoleVisibility := ty | return ← finish
  if paidRoleBinderName == `mount then return ← finish
  let c ← getLCtx
  let existingPaidInput ← if let some d := c.findFromUserName? paidRoleBinderName then pure (some d.toExpr)
    else if paidRoleVisibility.isInstImplicit then pure (c.findDecl? (fun d => if d.binderInfo.isInstImplicit then some d.toExpr else none))
    else pure none
  if let some x := existingPaidInput then return ← paidRoleSupplyArchive (paidRoleBinderBody.instantiate1 x) finish
  unless [`words,`dates,`accepted].contains paidRoleBinderName do throwError "Extra proper terminal operand {paidRoleBinderName}"
  withLocalDecl paidRoleBinderName paidRoleVisibility paidRoleBinderDomain fun x => paidRoleSupplyArchive (paidRoleBinderBody.instantiate1 x) finish

set_option maxRecDepth 18000 in
set_option maxHeartbeats 6400000 in
set_option cleanup.letToHave false in
run_cmd liftTermElabM do
  let schema ← getConstInfo ``fundedOriginalBallotWordTypes
  let donor ← getConstInfo ``purchased_final_role_archive
  let reader ← getConstInfo ``paidCapturedRoleFields
  withLCtx {} {} <| forallTelescope schema.type fun xs bundle => do
    let ballotNames := [`x₀,`z₀,`c₀]
    let fundedGeometryInputs ← xs.filterM fun x => do return !ballotNames.contains (← x.fvarId!.getDecl).userName.eraseMacroScopes
    let wordParts := mkAppN (Lean.mkConst schema.name) xs
    let target := mkApp2 (Lean.mkConst ``And) (mkProj bundle.consumeMData.getAppFn.constName! 0 wordParts) (mkProj bundle.consumeMData.getAppFn.constName! 1 wordParts)
    paidRoleSupplyArchive donor.type do
      let partialType ← instantiateForall reader.type xs
      let .forallE `din paidRoleInputDomain paidDinContinuation _ := partialType | throwError "Expected a purchased input"
      withLocalDeclD `din paidRoleInputDomain fun din => do
        let .forallE `restored _ paidRestoredContinuation _ := paidDinContinuation.instantiate1 din | throwError "Expected the restored input"
        let .forallE `date paidRoleDateDomain paidDateContinuation _ := paidRestoredContinuation.instantiate1 din | throwError "Expected registered rows"
        withLocalDeclD `date paidRoleDateDomain fun date => do
          let .forallE `scalar paidScalarDomain _ _ := paidDateContinuation.instantiate1 date | throwError "Expected scalar room"
          withLocalDeclD `scalarRoom paidScalarDomain fun scalar => do
            let mut spine := fundedGeometryInputs
            spine := spine.push scalar
            for n in [`words,`dates,`x₀,`z₀,`c₀,`accepted] do spine := spine.push (← roleFundingLocal n)
            spine := spine ++ #[din,date]
            let roleSuffix ← (spine.extract fundedGeometryInputs.size spine.size).mapM fun x => do
              return (← x.fvarId!.getDecl).userName.eraseMacroScopes
            unless roleSuffix == #[`scalarRoom, `words, `dates, `x₀, `z₀, `c₀, `accepted, `din, `date] do
              throwError "Invalid ordering of the funded role inputs: {roleSuffix}"
            let ty ← mkForallFVars spine target
            let proof ← mkLambdaFVars spine (← roleArchiveFromConcreteFunding target)
            if ty.hasFVar || proof.hasFVar || ty.hasMVar || proof.hasMVar || ty.hasLooseBVars || proof.hasLooseBVars then throwError "The historical purchased role proof must close over all inputs"
            addDecl (.thmDecl {
              name := `OAI.Hierarchy.DescentSixParty.SeedNamed.purchased_site_roles_arities
              levelParams := schema.levelParams
              type := ty
              value := proof })


open Lean Meta Elab Term

private def operandBinderKey (decl : LocalDecl) : Name :=
  if decl.binderInfo.isInstImplicit then `operandFieldInstance else decl.userName.eraseMacroScopes

private def operandLocalValues : MetaM (Array (Name × Lean.Expr)) := do
  let mut values := #[]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      values := values.push (operandBinderKey decl, decl.toExpr)
  return values

private def operandValue (values : Array (Name × Lean.Expr)) (key : Name) : MetaM Lean.Expr := do
  let some (_,purchasedParam) := values.find? (fun item => item.1 == key) | throwError "Missing original ballot parameter {key}"
  return purchasedParam

private def originalOperandArgs (info : ConstantInfo) (values : Array (Name × Lean.Expr)) : MetaM (Array Lean.Expr) :=
  forallTelescope info.type fun params _ => params.mapM fun boundParam => do
    operandValue values (operandBinderKey (← boundParam.fvarId!.getDecl))

private def indexedOperandFields (info : ConstantInfo) (actual : Array Lean.Expr) : MetaM (Array (Name × Lean.Expr)) :=
  forallTelescope info.type fun ps _ => do
    unless ps.size == actual.size do throwError "Expected all original site fields"
    let mut table := #[]
    for boundParam in ps, arg in actual do
      table := table.push (operandBinderKey (← boundParam.fvarId!.getDecl), arg)
    return table
private def archiveResetBody (e : Lean.Expr) : MetaM Lean.Expr := do
  let app := e.headBeta.consumeMData
  let .const fn us := app.getAppFn | throwError "Expected the stored reset to be a named application"
  let ci ← getConstInfo fn
  let some body := ci.value? | throwError "The stored reset {fn} has no definition"
  return ((body.instantiateLevelParams ci.levelParams us).beta app.getAppArgs).headBeta.consumeMData

/-- Read the registered physical reset under the original lastPorts wrapper. -/
private def archiveResetApplication (lastPorts : Lean.Expr) : MetaM Lean.Expr := do
  let ports := lastPorts.headBeta.consumeMData
  if ports.getAppFn.constName? == some ``DatePorts.reset then return ports
  let issued ← if ports.getAppFn.constName? == some ``DatePorts.resetPorts then pure ports else archiveResetBody ports
  unless issued.getAppFn.constName? == some ``DatePorts.resetPorts do
    throwError "Expected the registered previous ports, found {issued.getAppFn.constName?}"
  let result ← archiveResetBody issued
  unless result.getAppFn.constName? == some ``DatePorts.reset do throwError "The original registers do not expose their reset"
  return result

/-- Recover the exact original terminal reset input without elaborating its physical arguments. -/
private def restoredInputFromHistoricalPorts (space lastPorts : Lean.Expr) : MetaM Lean.Expr := do
  let reset ← archiveResetApplication lastPorts
  let some saved := reset.getAppArgs.back? | throwError "The registered reset has no input"
  let saved := saved.headBeta.consumeMData
  unless saved.getAppFn.constName? == some ``DatePorts.resetInputs do throwError "Unexpected registered input {saved.getAppFn.constName?}"
  unless saved.getAppArgs.back?.map Lean.Expr.consumeMData == some space.consumeMData do throwError "The reset input did not keep the selected space witness"
  return saved

private def historicalOperandWordFields (paid : Array (Name × Lean.Expr)) : MetaM (Array Lean.Expr) := do
  let schema ← getConstInfo ``fundedOriginalBallotWordTypes
  let schemaArgs ← originalOperandArgs schema paid
  let applied := (schema.value!.beta schemaArgs).consumeMData
  let wordTypes ← getConstInfo ``purchasedOriginalWordTypes
  unless applied.getAppFn.constName? == some wordTypes.name do throwError "Expected the funded original site word family"
  let packed := (wordTypes.value!.beta applied.getAppArgs).headBeta.consumeMData
  unless packed.isAppOfArity ``PurchasedWordTypes.mk 5 do throwError "Expected the selected original site word constructor"
  let words := packed.getAppArgs[3]!.consumeMData
  unless words.isAppOfArity ``OriginalSiteWords 61 do throwError "Expected all 61 captured site parameters"
  return packed.getAppArgs

private def registeredOperandArgs (ws : Array Lean.Expr) (dateInputTerm : Lean.Expr) : Array Lean.Expr :=
  ws.extract 0 27 ++ #[ws[36]!, ws[37]!] ++ ws.extract 40 55 ++ ws.extract 56 60 ++ #[dateInputTerm]

private def purchasedOperandStage (ws : Array Lean.Expr) : MetaM (Array (Name × Lean.Expr)) := do
  let keys ← indexedOperandFields (← getConstInfo ``OriginalSiteArgumentWords) ws
  let heap := ws[59]!.consumeMData
  let some acquiredMount := heap.find? (·.isAppOfArity ``originalRoleMount 12) | throwError "Missing physical role mount"
  let some countOutput := heap.find? (·.isAppOfArity ``DescentLowCountBook.output 5) | throwError "Missing original low-count capture"
  let ca := countOutput.getAppArgs
  return keys ++ #[(`past,ca[3]!), (`start,ca[1]!), (`count,ca[4]!), (`source,ca[2]!), (`mount,acquiredMount), (`mountedMemory_,heap)]

private def operandBindingType (info : ConstantInfo) (values : Array (Name × Lean.Expr)) (which : Name) : MetaM Lean.Expr :=
  forallTelescope info.type fun xs _ => do
    let mut inputs := #[]
    for boundParam in xs do
      let key := operandBinderKey (← boundParam.fvarId!.getDecl)
      if key == which then
        let remaining ← instantiateForall info.type inputs
        let .forallE _ inputType _ _ := remaining | throwError "Missing purchased operand input type"
        return inputType
      inputs := inputs.push (← operandValue values key)
    throwError "Unrecognized original operand input {which}"

private def acquiredOperandWidth (reader : ConstantInfo) (paid supplied : Array (Name × Lean.Expr)) : MetaM Lean.Expr := do
  let expected ← operandBindingType reader supplied `sizes
  let some (_,recordTerm,_) := expected.eq? | throwError "Expected the equality of bought and cubic operand records"
  let coords := recordTerm.getAppArgs
  let n := coords.size
  unless n >= 5 do throwError "Expected the last five physical record coordinates"
  let fundingTerm ← operandValue paid `funding
  let fundingType₀ ← inferType fundingTerm
  let fundingType := match fundingType₀.consumeMData with
    | .letE _ _ assigned body _ => (body.instantiate1 assigned).consumeMData
    | e => e
  unless fundingType.getAppFn.constName? == some ``OriginalWord do throwError "The original field buyer must contain its cubic record"
  let register ← getConstInfo ``OriginalWord.cubicRecords
  let reflTerm := mkApp (mkConst ``Nat.le_refl) coords[n-2]!
  let fixed := fundingType.getAppArgs ++ #[fundingTerm,← operandValue paid `siteCount,coords[n-4]!,coords[n-5]!,coords[n-3]!,coords[n-2]!,coords[n-1]!,reflTerm]
  return mkAppN (mkConst register.name) fixed

private def sourcedHistoricalOperandProof (paid : Array (Name × Lean.Expr)) (target : Lean.Expr) : MetaM Lean.Expr := do
  let pointer ← getConstInfo ``purchased_final_pointer_archive
  let pa ← originalOperandArgs pointer paid
  let vote := mkAppN (mkConst pointer.name) pa
  let archiveType := (← instantiateForall pointer.type pa).consumeMData
  unless archiveType.isAppOfArity ``Exists 2 do throwError "The paid pointer receipt must supply its original stored space"
  let ex := archiveType.getAppArgs
  let packageFields ← historicalOperandWordFields paid
  let words := packageFields[3]!.consumeMData
  let ws := words.getAppArgs
  let baseFields ← purchasedOperandStage ws
  let heap ← operandValue baseFields `mountedMemory_
  let acquiredMount ← operandValue baseFields `mount
  let din ← operandValue paid `din
  let r ← getConstInfo ``WideRegisteredDateRows
  let reg := registeredOperandArgs ws din
  let physical := (r.value!.beta reg).consumeMData
  unless physical.getAppFn.constName? == some ``PrimitiveDateRows do throwError "Missing original registered roster"
  let window ← getConstInfo ``paidActualArgumentWindow
  let bought ← originalOperandArgs window paid
  let spanProof := mkAppN (mkConst window.name) bought
  let spanTy := (← instantiateForall window.type bought).consumeMData
  let spanView ← getConstInfo spanTy.getAppFn.constName!
  let bounds := (spanView.value!.beta spanTy.getAppArgs).headBeta.consumeMData
  unless bounds.isAppOfArity ``And 2 do throwError "The purchased capture and mount bounds are missing"
  let early := mkAppN (mkConst ``And.left) (bounds.getAppArgs.push spanProof)
  let done_ := mkAppN (mkConst ``And.right) (bounds.getAppArgs.push spanProof)
  let reader ← getConstInfo ``mounted_site_argument_words
  let stage := baseFields ++ #[(`dateInput,din), (`rawPeers,physical.getAppArgs.back!), (`date,← operandValue paid `date), (`acquired,← operandValue paid `packets),
    (`matrixRead,← operandValue paid `matrixRead), (`early,early), (`done_,done_), (`replayFits,acquiredMount.getAppArgs.back!),
    (`wasMounted,← mkEqRefl heap), (`arities,← operandValue paid `arities)]
  withLocalDeclD `space ex[0]! fun sp => do
    let details := (ex[1]!.beta #[sp]).headBeta.consumeMData
    unless details.isAppOfArity ``And 2 do throwError "The original pointer must retain its ports and archive"
    let pieces := details.getAppArgs
    let some (_,_,actualPorts) := pieces[0]!.eq? | throwError "The paid pointer no longer reports its selected ports"
    unless pieces[1]!.getAppFn.constName? == some ``FinalPointerArchive do throwError "The physical pointer archive is missing"
    let restored ← restoredInputFromHistoricalPorts sp actualPorts
    withLocalDeclD `stored details fun stored => do
      let previous := mkAppN (mkConst ``And.right) #[pieces[0]!,pieces[1]!,stored]
      let restoredInputs := stage ++ #[(`originalInput,restored), (`previous,previous)]
      let sizes ← acquiredOperandWidth reader paid restoredInputs
      let all ← originalOperandArgs reader (restoredInputs.push (`sizes,sizes))
      let result := mkAppN (mkConst reader.name) all
      let handler ← mkLambdaFVars #[sp,stored] result
      return mkAppN (mkConst ``Exists.elim archiveType.getAppFn.constLevels!) #[ex[0]!, ex[1]!, target, vote, handler]

private partial def withHistoricalPointerInputs (cursor : Lean.Expr) (paid : Array (Name × Lean.Expr))
    (finish : Array (Name × Lean.Expr) → MetaM Unit) : MetaM Unit := do
  let .forallE binder domain body bi := cursor | return ← finish paid
  let key := if bi.isInstImplicit then `operandFieldInstance else binder.eraseMacroScopes
  if let some found := paid.find? (fun entry => entry.1 == key) then
    return ← withHistoricalPointerInputs (body.instantiate1 found.2) paid finish
  unless #[`acquireFor,`words,`dates,`accepted].contains key do throwError "Unfunded original pointer input {key}"
  withLocalDecl binder bi domain fun x =>
    withHistoricalPointerInputs (body.instantiate1 x) (paid.push (key,x)) finish

open Lean Elab Command in
set_option maxRecDepth 18000 in
set_option maxHeartbeats 6400000 in
set_option cleanup.letToHave false in
run_cmd liftTermElabM do
  let schema ← getConstInfo ``fundedOriginalBallotWordTypes
  let reader ← getConstInfo ``mounted_site_argument_words
  let pointer ← getConstInfo ``purchased_final_pointer_archive
  let registered ← getConstInfo ``WideRegisteredDateRows
  forallTelescope schema.type fun ballotXs _ => do
    let rows ← indexedOperandFields schema ballotXs
    withHistoricalPointerInputs pointer.type rows fun paid => do
      let windowStart := ballotXs.size-3
      let ballotInputs := ballotXs.extract windowStart ballotXs.size
      let three ← ballotInputs.mapM fun t => do return (← t.fvarId!.getDecl).userName.eraseMacroScopes
      unless three == #[`x₀,`z₀,`c₀] do throwError "Expected the acquired assignment and chosen ballot"
      let actualSource := (paid.find? (fun kv => kv.1 == `acquireFor)).map (·.2)
      let boughtInputs := ballotXs.extract 0 windowStart ++ actualSource.toList.toArray ++ #[← operandValue paid `words,← operandValue paid `dates] ++ ballotInputs ++ #[← operandValue paid `accepted]
      let packed ← historicalOperandWordFields paid
      let ws := packed[3]!.consumeMData.getAppArgs
      let stage ← purchasedOperandStage ws
      let inputType ← operandBindingType reader stage `dateInput
      withLocalDeclD `din inputType fun din => do
        let reg := registeredOperandArgs ws din
        let physical := (registered.value!.beta reg).consumeMData
        unless physical.isAppOf ``PrimitiveDateRows do throwError "Expected the registered physical roster"
        withLocalDeclD `date (mkAppN (mkConst registered.name) reg) fun date => do
          let paidDate := stage ++ #[(`dateInput,din), (`rawPeers,physical.getAppArgs.back!), (`date,date)]
          let packetsType ← operandBindingType reader paidDate `acquired
          withLocalDeclD `packets packetsType fun packets => do
            let matrixType ← operandBindingType reader (paidDate.push (`acquired,packets)) `matrixRead
            withLocalDeclD `matrixRead matrixType fun matrixRead => do
              withLocalDeclD `arities packed[1]! fun arities => do
                let all := boughtInputs ++ #[din,date,packets,matrixRead,arities]
                let selected := paid ++ #[(`din,din),(`date,date),(`packets,packets),(`matrixRead,matrixRead),(`arities,arities)]
                let used ← sourcedHistoricalOperandProof selected packed[2]!
                let type ← mkForallFVars all packed[2]!
                let proof ← mkLambdaFVars all used
                addDecl (.thmDecl {name := `OAI.Hierarchy.DescentSixParty.SeedNamed.purchased_final_site_arguments, levelParams := schema.levelParams, type := type, value := proof})


open Lean Meta Elab Command

/-- Read the original funding binders with their declared visibility. Each result uses
the same selected ballot, dated physicalSiteConstructor registers and captured memory. -/
private def paidAssemblyBinder (context : Array Lean.Expr) (name : Name)
    (kind : BinderInfo) : MetaM Lean.Expr := do
  for actual in context do
    let decl ← actual.fvarId!.getDecl
    if decl.userName.eraseMacroScopes == name.eraseMacroScopes then return actual
  if kind.isInstImplicit then
    for actual in context do
      if (← actual.fvarId!.getDecl).binderInfo.isInstImplicit then return actual
  throwError "Missing original site parameter {name}"

private def paidAssemblyApplication (decl : ConstantInfo) (context : Array Lean.Expr)
    (stopAt : Option Name := none) : MetaM (Lean.Expr × Lean.Expr) := do
  let mut value := Lean.mkConst decl.name
  let mut ty := decl.type
  while let .forallE n dom body bi := ty.consumeMData do
    if stopAt == some n.eraseMacroScopes then return (value, dom)
    let x ← paidAssemblyBinder context n bi
    value := mkApp value x
    ty := body.instantiate1 x
  if stopAt.isSome then throwError "Missing original site binder {stopAt} in {decl.name}"
  return (value, ty)


/- On the funded accepted ballot, the original role, arity, and first-use operand
are values in the same selected primitive image of memory. -/
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5200000 in
set_option cleanup.letToHave false in
run_cmd liftTermElabM do
  let siteArgumentDecl ← getConstInfo ``purchased_final_site_arguments
  let siteRoleDecl ← getConstInfo ``purchased_site_roles_arities
  let siteWordSchema ← getConstInfo ``fundedOriginalBallotWordTypes
  forallTelescope siteArgumentDecl.type fun xs _ => do
    let some arities := xs.back? | throwError "Missing funded arity input"
    unless (← arities.fvarId!.getDecl).userName.eraseMacroScopes == `arities do
      throwError "The operand proof must end in the measured arity input"
    let sharedSiteInputs := xs.pop
    let (_, scalarInputType) ← paidAssemblyApplication siteRoleDecl sharedSiteInputs (some `scalarRoom)
    let some exteriorInputOffset := (← sharedSiteInputs.mapM fun x => return (← x.fvarId!.getDecl).userName.eraseMacroScopes).idxOf? `x₀
      | throwError "Missing selected original exterior ballot"
    withLocalDeclD `scalar scalarInputType fun scalar => do
      let mut siteRolesValue := Lean.mkConst siteRoleDecl.name
      let mut siteRoleType := siteRoleDecl.type
      while let .forallE n _ body bi := siteRoleType.consumeMData do
        let x ← if n.eraseMacroScopes == `scalarRoom then pure scalar else paidAssemblyBinder sharedSiteInputs n bi
        siteRolesValue := mkApp siteRolesValue x
        siteRoleType := body.instantiate1 x
      let (suppliedSiteFields, _) ← paidAssemblyApplication siteWordSchema sharedSiteInputs
      let (measuredOperand, _) ← paidAssemblyApplication siteArgumentDecl sharedSiteInputs (some `arities)
      let physicalSiteConstructor ← getConstInfo ``fundedSiteWordsAtCapturedMemory
      let fundedCompleteInputs := suppliedSiteFields.getAppArgs ++ #[siteRolesValue, measuredOperand]
      let result ← instantiateForall physicalSiteConstructor.type fundedCompleteInputs
      unless result.isAppOfArity ``OriginalSiteWords 61 do
        throwError "The paid original result must expose all 61 physical fields"
      let proof := mkAppN (Lean.mkConst physicalSiteConstructor.name) fundedCompleteInputs
      let publicInputs := sharedSiteInputs.extract 0 exteriorInputOffset ++ #[scalar] ++ sharedSiteInputs.extract exteriorInputOffset sharedSiteInputs.size
      let ty ← mkForallFVars publicInputs result
      let val ← mkLambdaFVars publicInputs proof
      addDecl (.thmDecl {
        name := `OAI.Hierarchy.DescentSixParty.SeedNamed.original_site_words
        levelParams := siteArgumentDecl.levelParams, type := ty, value := val })


end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI
attribute [local irreducible] Hierarchy.DescentSixParty.SeedNamed.Origin.source

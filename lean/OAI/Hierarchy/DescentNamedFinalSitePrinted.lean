import OAI.Hierarchy.DescentNamedOriginalEarnedSites
import OAI.Hierarchy.DescentNamedArchivedRole
import OAI.Hierarchy.DescentFinalArgumentCapacity
import OAI.Hierarchy.DescentOrdinaryRegisteredWordRoom
import OAI.Hierarchy.DescentTerminalRegisteredRange
import OAI.Hierarchy.DescentTerminalArchivedSliceChart
import OAI.Hierarchy.DescentTerminalPrintedFieldRoom

namespace OAI
/-! The selected reset's role fields on the primitive scanner's actual input. -/
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
set_option maxHeartbeats 800000
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin Branch.archive Branch.bundleShape

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
variable {w K:ℕ} (payloadBits:ℕ) (fit:(S.firstWidth G.b (W*piece))<2^w)
local notation "chart" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
local notation "fmt" => Branch.geometryFormat G S k g p tail q R rot headerRows paidRows
local notation "pre" => Branch.preflightSpec X G S k g p tail ({fmt with binSize:=W}:Branch.PreflightFormat)
variable (begin_ rom : ℕ) (peer:Bank) (old:Fin ((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).scalar.blocks→Fin (2*((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).cap)→Bank)
    (org:ℕ) (homes:Bank) (other:AddressPlan.Input)
variable {arity groups stride oldTags:ℕ} (codec:DescentEpochTagKeys.Codec (Label G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) oldTags)
local notation "tagCount" => DescentBundleTagKeys.capacity oldTags arity groups p stride
local notation "V" => (⟨q,tagCount,cap,nodeCap,cap,p,groupsAt⟩:Home.Format)
local notation "B" => (pre).pageBits
variable (lo packWidth : ℕ)
local notation "steps" => (chart).layout
local notation "Full" => DescentTerminalFullPins.Candidate ((chart).Pin⊕Hidden E₀ j rest s) K W q piece rawWords
variable (all : (DescentTerminalFullPins.Candidate (((normalizedPackedChart X G S ordinary reset branch positive room shorten w fit)).Pin⊕Hidden (Fintype.card (Port P X.width)) j rest (S.firstWidth G.b (W*piece))) K W q piece rawWords)→Bool)

variable (head : ℕ) (short : ((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).vertices*DescentTerminalVertexFields.span (((⟨q,(DescentBundleTagKeys.capacity oldTags arity groups (W*piece) stride),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).publicArity (((⟨q,(DescentBundleTagKeys.capacity oldTags arity groups (W*piece) stride),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).roles (((⟨q,(DescentBundleTagKeys.capacity oldTags arity groups (W*piece) stride),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).privateWords (((⟨q,(DescentBundleTagKeys.capacity oldTags arity groups (W*piece) stride),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).nodes (((⟨q,(DescentBundleTagKeys.capacity oldTags arity groups (W*piece) stride),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).addresses (((⟨q,(DescentBundleTagKeys.capacity oldTags arity groups (W*piece) stride),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).piece≤(((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).pageBits))







local notation "compact" => end_ (lo+extent packWidth steps) G.C packWidth
variable (fence:ℕ) (count:ℕ→ℕ) (plan:Reel)
variable (primitive m:Memory w)
variable (original:Port ((2^(j+(j+rest))*(S.firstWidth G.b (W*piece)))*P) (copiesWidth (2^(j+(j+rest))*(S.firstWidth G.b (W*piece))) X.width)→Bool)

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
    (datedMem : Memory w)

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
    (snapshots:=snapshots) (roleBase:=roleBase) (dateInput:=dateInput) (datedMem:=datedMem)
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
open private DescentTerminalFixedSlices.Phase.inside from OAI.Hierarchy.DescentTerminalFixedSlices

include base in
/-- All six packed columns survive from the chronological slice pass to the native primitive
scanner. The earlier replay cannot overwrite any address produced by the last reset. -/
theorem final_site_slice_source {rawPeers} (date:physicalRows rawPeers) :
    (∀a<sliceEnd,primitiveImage_ a=(datePhase).memory earlyFloor (earlyImage datedMem) a) ∧
    (∀a<(dateOut).metadataEnd dateOrigin,earlyImage datedMem a=datedMem a) ∧
    (∀field block,((datePhase).chart field block).Fits ((dateOut).metadataEnd dateOrigin) (dateHardware).hosts w) ∧
    2^(datePhase).digits<2^w ∧ sliceEnd<2^w ∧ ∀f,roleBankBits f≤w := by
  have early := Branch.scheduled_base_le_early S k tail replayBase j rest s datePorts
  have inside:=(DescentTerminalFixedSlices.Phase.inside datePhase earlyFloor)
  obtain ⟨first,second,third,last_,_⟩:=(dateCalendar).addresses sliceEnd censusBase
  have sliceLower:sliceEnd≤censusBase:=(first.trans (second.trans third)).trans (Nat.le_add_right ..)
  have sliceRoom:sliceEnd<2^w:=(sliceLower.trans last_).trans_lt replayRoom
  have top:=Phase.scheduled_layout G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
    operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor date.lastDate
  have low:(dateOut).metadataEnd dateOrigin≤replayBase:=top.2.2.2.2.2.trans_le date.tailRoom
  have one:=Phase.scheduled_one G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
    operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor date.lastDate base date.signedWidth
  have prefix_:=Branch.scheduled_original_preflight X G S base ordinary.radix g p q R rot headerRows paidRows
    board dateAge f dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress
    rosterBank datedFloor j rest s replayBase matrixTable dateTag dateRotation snapshots roleBase replayRoom
    date.lastDate date.previousBlocks date.wordRoom date.positiveWord date.occupied date.rotations date.matrix
    (date.tailRoom.trans early) date.signedWidth date.snapshotsFit date.roleTable datedMem
  have earned:=native_earned_layout (base:=base) (dateTag:=dateTag) (replayRoom:=replayRoom) (date:=date)
  have weights:sliceEnd≤(dateSpec).weights censusBase:=sliceLower.trans
    (((dateSpec).cohort_le censusBase).trans (((dateSpec).layers censusBase).1.trans ((dateSpec).layers censusBase).2.1))
  have earlyRun:=Calendar.early_run S k tail replayBase dateTag dateRotation j rest s datePorts matrixTable datedMem
    date.positiveWord date.rotations date.matrix (inside.1.trans_lt sliceRoom)
  have mid:(datePhase).stop ((dateOut).metadataEnd dateOrigin)≤ sliceEnd:=by
    unfold Phase.stop DescentTerminalCompiledPrefix.AddressPlan.sliceStop
      DescentTerminalSliceShelf.fence DescentTerminalSliceShelf.stage DescentTerminalPointerDigits.Gather.rom
      DescentOperandStateBanks.guard
    have bound:=low.trans early
    omega
  refine ⟨fun a near=>(earned.2.1 a (near.trans_le weights)).symm.trans (prefix_.2.2.1 a near),
    fun a near=>earlyRun.2.2 a (.inl (near.trans_le low)),?_,inside.2.trans_lt sliceRoom,sliceRoom,?_⟩
  · exact (datePhase).fits _ le_rfl one (mid.trans_lt sliceRoom)
  · exact DescentTerminalRoleTables.field_word_room roleBankBits date.roleTable
      (early.trans_lt (inside.1.trans_lt sliceRoom))

open DescentTerminalSliceShelf DescentTerminalSliceRuns DescentDatedPriorOperand
open DescentLocalArchiveOrder DescentRetainedRangeDigits
open Chronology DescentBundleHistory

variable {restoredInput : ((PhysicalReset.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset)   (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).DateInputs (((PhysicalReset.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset)   (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).stageStart datedFloor) w}
local notation "lastPorts_" => DatePorts.reset dateMachine ((dateMachine).stageStart datedFloor) restoredInput
local notation "baseBits_" => (Branch.archive X G S b positive).bit
local notation "baseOrder_" => Branch.localNodes X G S b positive
local notation "one_" => le_max_left 1 (max reset.bitsR (C*reset.bitsR))
local notation "baseShape_" => Branch.bundleShape X G S b positive one_
local notation "encoder_" => Palette.atLeaf X G S ordinary reset branch positive room shorten c
local notation "slot_" i:arg v:arg u:arg => (DescentTerminalChronologicalBooks.ordinal ((liveRanks i).atom v) u).castLE (nodeFit i v)
local notation "venue_" home:arg site:arg => (homeOrd).node home site
local notation "block_" v:arg => (b).target.placement.block v
local notation "observed_" home:arg site:arg => DescentTerminalCombinedRole.observed (n:=dateColors) (A:=max 8 (2^S.capGain)) (G:=cap)
  («p»:=p) («R»:=R) (N:=nodeCap) (M:=groupsAt) roleBanks primitiveImage_
    ((finProdFinEquiv (block_ (venue_ home site),home)).val:Computability.VPVNP.BurstRAM.Word w)

open Chronology DescentRetainedRangeDigits DescentTerminalSliceShelf
set_option maxHeartbeats 4300000
open DescentTerminalSliceRuns DescentOperandStateBanks
private def printedAtResident {n A G : ℕ} {T Nodes : Type} (dictionary : Codec T n)
    (read : Nodes → DescentTerminalCombinedRole.Fields A G) (tag : Nodes → T)
    (slices : Nodes → List (List SliceCode)) : Prop :=
  ∀u, DescentTerminalCombinedRole.Printed dictionary (read u) (tag u) (slices u)

include base width age in
/-- The selected scheduled reset supplies the six genuine scalar role fields at each
occupied site of the primitive scanner, including retained and newly introduced gates. -/
theorem final_site_printed_source {rawPeers} (date:physicalRows rawPeers)
    (places:DatePorts.RangeRoom lastPorts_ (b).target baseBits_) {ptr flags}
    (archive:DatePorts.ArchiveRead lastPorts_ (b).target baseBits_ baseOrder_ places baseShape_ rot
      (encoder_).atNode ptr flags datedMem) :
    ∀ (home : Fin H₀) (site : Fin (Fintype.card ((homeOrd).Nodes home))),
      printedAtResident liveCodec
        (fun u : (liveRec home site).Node => DescentTerminalCombinedRole.fields (DescentTerminalCombinedRole.node
          (observed_ home site) ((b).target.placement.pos (venue_ home site)).1 (slot_ home site u)))
        (fun u => ((trueLeaf).bit (venue_ home site)).tag u)
        (fun u => ((trueLeaf).shape (venue_ home site)).sliceFields u) :=by
  have reading := final_site_slice_source (base:=base) (dateTag:=dateTag) (replayRoom:=replayRoom) (date:=date)
  have later:=reading.1
  have earlier:=reading.2.1
  have guarded:=reading.2.2.1
  have off:=reading.2.2.2.1
  have shelfRoom:=reading.2.2.2.2.1
  have fieldsFit:=reading.2.2.2.2.2
  have geometry:=Phase.scheduled_layout G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
    operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor date.lastDate
  have blocks:(dateHardware).blocks=2^k:=geometry.1
  have hosts:(dateHardware).hosts=H₀:=geometry.2.1
  have groups:(dateHardware).groups=groupsAt:=by
    change S.groupCount (dateAge+1)=_
    rw [date.lastDate]
  have nodes:(dateOut).nodes=nodeCap:=geometry.2.2.2.1
  have axes:=PhysicalReset.scheduled_range_layout G S board k tail dateAge p f g R dateDegree datePayload
    ordinaryAt rot s Z operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
    ((dateMachine).stageStart datedFloor) restoredInput date.previousBlocks
  have metadata:(lastPorts_).metadataChart=(dateOut).metadata.chart:=
    congrArg (fun cuts=>(⟨cuts,(dateOut).nodes,(dateOut).sheets.hosts,(dateOut).sheets.groups,
      (dateOut).nodeBits,(dateHardware).lanes⟩:DescentDatedNodeMetadata.Chart)) (congrArg (2^·) date.previousBlocks)
  have hostD:H₀=(lastPorts_).operandHosts:=hosts.symm
  have pitch:(lastPorts_).operandLanes=(lastPorts_).venue.groups:=by
    change (dateVenue).signedLanes=S.groupCount (dateAge+1)
    rw [date.lastDate,date.signedWidth]
  have rolePitch:(lastPorts_).roleLanes=(lastPorts_).venue.groups:=pitch
  let bg:2^k=(dateHardware).blocks:=(congrArg (2^·) places.radix).trans (congrArg DescentDatedPriorOperand.Layout.blocks axes)
  let src:=fun (f:Fin (DescentTerminalSliceRuns.Columns (dateOut).argumentSlots)) (rowIndex:DescentColonies.Block k)=>(datePhase).chart f (rowIndex.cast bg)
  let d:=(datePhase).digits
  let lastStage:=(dateOut).metadataEnd dateOrigin
  have floorRoom:lastStage≤earlyFloor:=geometry.2.2.2.2.2.trans_le (date.tailRoom.trans (Branch.scheduled_base_le_early S k tail replayBase j rest s datePorts))
  have prior (field block) : (src field block).Fits lastStage H₀ w:=by
    simpa only [←hosts] using guarded field (block.cast bg)
  have one:=Phase.scheduled_one G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
    operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor date.lastDate base date.signedWidth
  have source (field block) : (src field block).Fits earlyFloor H₀ w:=by
    simpa only [←hosts] using (datePhase).fits earlyFloor floorRoom one shelfRoom field (block.cast bg)
  have dataWidth : physicalWidth (lastPorts_).venue.groups (dateOut).nodes (printedBits G s Z rot) (dateOut).nodeBits=d:=rfl
  have wide : d≤w:=((Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp off).le
  have valFits : (dateOut).argumentSlots<2^(dateOut).nodeBits:=
    DescentOperandWidth.registered_arguments G S k tail R dateDegree p
  have endEq : DescentTerminalSliceShelf.fence earlyFloor (DescentTerminalSliceRuns.Columns (dateOut).argumentSlots) d ((2^k)*H₀)=sliceEnd:=by
    change _=DescentTerminalSliceShelf.fence earlyFloor (DescentTerminalSliceRuns.Columns (dateOut).argumentSlots) d ((dateHardware).blocks*(dateHardware).hosts)
    rw [blocks,hosts]
  have stored:=role_memory_reindex bg hosts groups nodes earlyFloor (datePhase).chart s Z (max 8 (2^S.capGain))
    cap p R G rot (datedWidths dateOut) (earlyImage datedMem) (d:=d)
  have sourcesEq : (fun f:Fin 6=>DescentTerminalSliceShelf.field earlyFloor (DescentTerminalSliceRuns.Columns (dateOut).argumentSlots) d
      (2^k*H₀) f.val)=(datePhase).banks earlyFloor:=by
    funext field
    change _=DescentTerminalSliceShelf.field earlyFloor (DescentTerminalSliceRuns.Columns (dateOut).argumentSlots) d
      ((dateHardware).blocks*(dateHardware).hosts) field.val
    rw [blocks,hosts]
  intro home site u
  have fits:(repeatFields (((trueLeaf).shape (venue_ home site)).sliceFields u).flatten).length≤(dateOut).argumentSlots:=by
    let shapeAt := (trueLeaf).shape (venue_ home site)
    have columns := congrArg List.length (DescentRetainedRangeDigits.layout shapeAt u)
    have count := DescentRetainedRangeDigits.length shapeAt u positive
    exact (columns.trans count).trans_le
      (Branch.final_argument_capacity X G S b positive one_ age branch (venue_ home site) u)
  have computed:=normalized_archived_role (d:=d) X G S ordinary reset branch positive room shorten c
    dateMachine ((dateMachine).stageStart datedFloor) restoredInput places axes metadata
    (datePhase).tokenBlocks (datePhase).countBlocks base width age earlyFloor roleBase lastStage
    datedMem (earlyImage datedMem) primitiveImage_ home site archive hostD nodes.symm rfl pitch rolePitch
    (dataWidth.trans_le wide) dataWidth.le valFits prior earlier source off (endEq.trans_lt shelfRoom)
    fieldsFit (fun a ha=>(later a (ha.trans_le endEq.le)).trans (congrFun stored.symm a)) u fits
  let publishedAt (banks : Fin 6 → Bank) : Prop := DescentTerminalCombinedRole.Printed liveCodec
    (DescentTerminalCombinedRole.fields (DescentTerminalCombinedRole.node
      (DescentTerminalCombinedRole.observed (n:=dateColors) (A:=max 8 (2^S.capGain)) (G:=cap)
        («p»:=p) («R»:=R) (N:=nodeCap) (M:=groupsAt) (DescentTerminalRoleTables.role roleBankBits banks roleBase)
        primitiveImage_ ((finProdFinEquiv (block_ (venue_ home site),home)).val:Computability.VPVNP.BurstRAM.Word w))
      ((b).target.placement.pos (venue_ home site)).1 (slot_ home site u)))
    (((trueLeaf).bit (venue_ home site)).tag u) (((trueLeaf).shape (venue_ home site)).sliceFields u)
  have measured : publishedAt (fun field : Fin 6 => DescentTerminalSliceShelf.field earlyFloor
      (DescentTerminalSliceRuns.Columns (dateOut).argumentSlots) d (2^k*H₀) field.val) := computed
  exact Eq.mp (congrArg publishedAt sourcesEq) measured




local notation "siteShelf" => MaskAllocation.shelf (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap)
  («p»:=p) (groups:=groupsAt) ((dateSpec).channels censusBase) ((dateSpec).maskBase censusBase)
local notation "siteAddr" home:arg site:arg => finProdFinEquiv
  (((b).target.placement.pos (venue_ home site)).1,block_ (venue_ home site))
local notation "siteWord" home:arg site:arg key:arg => venueField (cellAt (measured (q:=q) (t:=allTags)
  (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) siteShelf primitiveImage_ home) (siteAddr home site)) key

local notation "originalWordField" form:arg => form
  (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive)
  (room:=room) (shorten:=shorten) (c:=c) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit)
  (qh:=qh) (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords)
  (headerRows:=headerRows) (paidRows:=paidRows) (pool:=pool) (raw:=raw) (board:=board) (dateAge:=dateAge)
  (dateDegree:=dateDegree) (datePayload:=datePayload) (ordinaryAt:=ordinaryAt)
  (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previousDate:=previousDate)
  (priorAddress:=priorAddress) (rosterBank:=rosterBank) (datedFloor:=datedFloor) (replayBase:=replayBase)
  (matrixTable:=matrixTable) (dateTag:=dateTag) (dateRotation:=dateRotation) (snapshots:=snapshots)
  (roleBase:=roleBase) (datedMem:=datedMem) (replayRoom:=replayRoom)

/-- At any scalar budget height, the mounted tables and retained archive supply the original role and arity words. -/
theorem final_site_roles_arities_at_height {scalarHeight : ℕ} {rawPeers} (date:physicalRows rawPeers)
    (wideShort:(pre).vertices*span q allTags cap nodeCap cap p≤(pre).pageBits)
    (scalar:EarnedScalarArguments j s p q W allTags (dateSpec).pageBits (dateSpec).printBits scalarHeight w)
    (startRoom:replayBase<2^w) («copied»:Memory w)
    (mounted:datedMem=(originalRoleMount G rot S p R roleBase replayBase date.roleTable startRoom).phase.image «copied»)
    (places:DatePorts.RangeRoom lastPorts_ (b).target baseBits_) {ptr flags}
    (archive:DatePorts.ArchiveRead lastPorts_ (b).target baseBits_ baseOrder_ places baseShape_ rot
      (encoder_).atNode ptr flags datedMem) :
    originalWordField OriginalSiteRoleWords ∧ originalWordField OriginalSiteArityWords :=
  earned_site_role_scan_at_height (scalarHeight:=scalarHeight) (base:=base) (dateTag:=dateTag) (replayRoom:=replayRoom) (wideShort:=wideShort) (date:=date)
    (scalar:=scalar) (startRoom:=startRoom) («copied»:=«copied») (mounted:=mounted)
    (printed:=final_site_printed_source (wFit:=wFit) (qFit:=qFit) (qh:=qh) (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (pool:=pool) (raw:=raw)
      (base:=base) (width:=width) (age:=age) (dateTag:=dateTag) (replayRoom:=replayRoom) (date:=date) (places:=places) (archive:=archive))

/-- The funded site's physical role and arity are read from the two mounted native
tables and the surviving terminal archive at the same registered date. -/
theorem final_site_roles_arities {rawPeers} (date:physicalRows rawPeers)
    (wideShort:(pre).vertices*span q allTags cap nodeCap cap p≤(pre).pageBits)
    (scalar:EarnedScalarArguments j s p q W allTags (dateSpec).pageBits (dateSpec).printBits h w)
    (startRoom:replayBase<2^w) («copied»:Memory w)
    (mounted:datedMem=(originalRoleMount G rot S p R roleBase replayBase date.roleTable startRoom).phase.image «copied»)
    (places:DatePorts.RangeRoom lastPorts_ (b).target baseBits_) {ptr flags}
    (archive:DatePorts.ArchiveRead lastPorts_ (b).target baseBits_ baseOrder_ places baseShape_ rot
      (encoder_).atNode ptr flags datedMem) :
    originalWordField OriginalSiteRoleWords ∧ originalWordField OriginalSiteArityWords :=
  @final_site_roles_arities_at_height F _ cp P X G S k cut tail n h C
    f g W q piece ordinary reset branch positive room shorten c j
    rest base width age wFit qFit qh template sitesPositive rawWords headerRows paidRows pool
    raw w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank
    datedFloor replayBase matrixTable dateTag dateRotation snapshots roleBase datedMem dateInput replayRoom restoredInput h rawPeers
    date wideShort scalar startRoom «copied» mounted places ptr flags archive

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

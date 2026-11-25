import OAI.Hierarchy.DescentTerminalPlacedChip
import OAI.Hierarchy.DescentEarnedStageInvoice
import OAI.Hierarchy.DescentDatedSeedAppendedProfile
import OAI.Hierarchy.DescentDatedSeedInitialHeld
import OAI.Hierarchy.DescentOriginalFundedCourse
import OAI.Hierarchy.DescentTerminalPaidCensusRoom
import OAI.Hierarchy.DescentNamedScheduledPacketHomes
import OAI.Hierarchy.DescentTerminalReadoutBounds
import OAI.Hierarchy.DescentTerminalTrailingPrice
import OAI.Hierarchy.DescentNamedWideStageHost
import OAI.Hierarchy.DescentNamedScheduledWideFlight

namespace OAI
/-! # One funded native procedure for every external and hidden assignment -/

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
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g W q piece : ℕ}
set_option hygiene false
local notation "p" => W*piece
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0<W*piece) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
variable (c : (Epochs.finish G _ _ (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose).Choice)
local notation "b" => SeedNamed.issued X G S ordinary reset branch positive room shorten c

open Chronology DescentExteriorReplay DescentExteriorShelf
attribute [local irreducible] SeedNamed.issued
set_option maxHeartbeats 700000
set_option maxRecDepth 6144

private theorem issued_terminal_snapshot_labels (snapshots : Snapshots k) (rankDirectory : ℕ → Bank)
    (rankShape : snapshots = Chronology.SnapshotCalendar reset (Chronology.kindCalendar S.rounds S.height)
      (capCalendar G.b S.rounds g S.height) rankDirectory) :
    (b).path.snapshotLabels snapshots ∧ ∀ i < S.length, S.hostSize i ≤ snapshots.hosts i := by
  subst snapshots
  have rotor : (b).path.OnlyRotor (RotorSpec.ofRates reset) := by
    delta SeedNamed.issued
    exact ((cert).choose_spec.2.2.choose_spec.choose_spec c).choose_spec.2.2.1.2
  exact ⟨Branch.original_snapshot_labels (X:=X) (G:=G) (S:=S) («b»:=b) reset rankDirectory rotor,
    fun _ _ => le_rfl⟩

end
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
set_option maxRecDepth 12288
set_option maxHeartbeats 1500000
set_option cleanup.letToHave false
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
variable (replayRoom : ((replayCalendar X S k tail j rest snapshots)).stop (((((preflightSpec X G S k g (W*piece) tail (geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows))).scanPages (((replayCalendar X S k tail j rest snapshots)).packetEnd (((Phase.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset)   operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).stop (DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail replayBase j rest (S.firstWidth G.b (W*piece)) (Fintype.card (Port P X.width))))) q)).stop)<2^w)

local notation "dateEntry" => (dateCalendar).memory sliceEnd censusBase replayRoom ((datePhase).memory earlyFloor (earlyImage datedMem))
local notation "primitiveImage_" => (@nativePrimitive F _ cp P X G S k cut tail n h C f g W q piece reset j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateTag dateRotation snapshots roleBase datedMem replayRoom)
local notation "datedDecoder" => Branch.decodeBook S G base ordinary.radix p q 3
  (dateSpec).cap (dateSpec).printBits (by decide)
local notation "bookImage_" => (@nativeBooks F _ cp P X G S k cut tail n h C f g W q piece ordinary reset j rest base headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateTag dateRotation snapshots roleBase datedMem replayRoom)
local notation "dateHomes" => (dateCalendar).homes sliceEnd
local notation "postEntry_" => Branch.postEarlyPreflightMemory X G S base ordinary.radix g p q R rot headerRows paidRows
  j rest s replayBase datePhase snapshots blockCast roleBase peerBank paidBank actorBank wingBank replayRoom
  (earlyImage datedMem)
local notation "bookControl" x:arg => portTable (G:=4) («V»:=(x).vertices) («M»:=(x).vertices*(x).arguments)
  (A:=(x).arguments) (a:=Book.tokenBits ((x).vertices*(x).arguments)) q
local notation "postBook" x:arg => (x).afterSiteControls censusBase q p peerBank wingBank
  (((x).scanPages lookupBase q).total) (((x).scanPages lookupBase q).modulo) dateHomes
  (((x).scanPages lookupBase q).boundaries)
  (((x).controls censusBase).after (bookControl x) (Book.expression ((x).parts censusBase)) bookImage_)

local notation "liveGrid" => (b).target.placement
local notation "liveHosts" => (b).target.vertex.trans (Fin.castLEEmb (b).target.valid.host)
local notation "dateMasks" => Venue.actual liveGrid (Function.Embedding.refl _) liveHosts
local notation "physicalRows" => PrimitiveDateRows (q:=q) (j:=j) (rest:=rest) (W:=W) (piece:=piece) (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive)
    (room:=room) (shorten:=shorten) (c:=c) (board:=board) (dateAge:=dateAge) (dateDegree:=dateDegree)
    (datePayload:=datePayload) (ordinaryAt:=ordinaryAt) (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes)
    (previousDate:=previousDate) (priorAddress:=priorAddress) (rosterBank:=rosterBank) (datedFloor:=datedFloor)
    (replayBase:=replayBase) (matrixTable:=matrixTable) (dateRotation:=dateRotation)
    (snapshots:=snapshots) (roleBase:=roleBase) (dateInput:=dateInput) (datedMem:=datedMem)
    (headerRows:=headerRows) (paidRows:=paidRows)
local notation "datedRowsChecked" O:arg H:arg Q:arg test:arg mask:arg reelMask:arg nodeTest:arg => WideObservedSourcesWith (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (pool:=pool) (raw:=raw) (payloadBits:=payloadBits) (fit:=fit) (begin_:=censusBase) (rom:=rom)
      (peer:=peerBank) (old:=wingBank) (org:=O) (homes:=H) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=fence) (count:=count) (plan:=plan) (codec:=codec) (short:=short) (all:=all) (c:=c)
      (primitive:=primitiveImage_) (m:=Q) (original:=original) test mask reelMask nodeTest
local notation "datedRowsRaw" O:arg H:arg Q:arg test:arg mask:arg reelMask:arg => datedRowsChecked O H Q test mask reelMask id
local notation "datedRowsCore" O:arg H:arg Q:arg test:arg mask:arg => datedRowsRaw O H Q test mask id

local notation "paidCapture_" => WideCapturedRows (X:=X) (G:=G) (S:=S) (ordinary:=ordinary)
  (reset:=reset) (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (c:=c)
   (template:=template) (sitesPositive:=sitesPositive)
  (rom:=rom) (other:=other) (head:=head) (count:=count) (rawWords:=rawWords) (headerRows:=headerRows) (paidRows:=paidRows) (payloadBits:=payloadBits)
  (fit:=fit) (begin_:=censusBase) (peer:=peerBank) (old:=wingBank) (org:=lookupBase)
  (homes:=dateHomes) (lo:=lo) (packWidth:=packWidth) (all:=all) (fence:=fence) (plan:=plan)
  (K:=K) (m:=bookImage_) (original:=original) (arity:=arity) (groups:=groups) (stride:=stride) (oldTags:=oldTags)
local notation "paidPackets_" => WideMeasuredPackets (X:=X) (G:=G) (S:=S) (ordinary:=ordinary)
  (reset:=reset) (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (c:=c)
  (base:=base) (width:=width) (headerRows:=headerRows) (paidRows:=paidRows)
  (begin_:=censusBase) (peer:=peerBank) (old:=wingBank) (org:=lookupBase) (homes:=dateHomes)
  (primitive:=primitiveImage_) (m:=bookImage_)
local notation "datedRowsWith" O:arg H:arg Q:arg test:arg => datedRowsCore O H Q test id
local notation "publishedAt_" O:arg H:arg Q:arg => WideObservedSources (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (pool:=pool) (raw:=raw) (payloadBits:=payloadBits) (fit:=fit) (begin_:=censusBase) (rom:=rom)
      (peer:=peerBank) (old:=wingBank) (org:=O) (homes:=H) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=fence) (count:=count) (plan:=plan) (codec:=codec) (short:=short) (all:=all) (c:=c)
      (primitive:=primitiveImage_) (m:=Q) (original:=original)
local notation "inputsAt_" O:arg H:arg Q:arg => datedRowsWith O H Q physicalRows
local notation "trueRoster" => (b).target.terminalRoster (b).target.valid.host
local notation "ownsRoster" => fun raw => raw=trueRoster
local notation "inputs_" => inputsAt_ org homes m
local notation "published_" => publishedAt_ org homes m


set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
attribute [local irreducible] SeedNamed.issued normalizedPackedChart
local notation:max "packetPost" readImage:arg => Branch.postEarlyPreflightMemory X G S base ordinary.radix g p q R rot headerRows paidRows
  j rest s replayBase datePhase snapshots blockCast roleBase peerBank paidBank actorBank wingBank replayRoom (earlyImage readImage)
local notation:max "packetPrimitive" readImage:arg => Branch.fixedPreflightPrimitive X G S («k»:=k) («tail»:=tail) g p q R rot
  headerRows paidRows censusBase lookupBase w paidBank actorBank wingBank matrixFloor roleBase ((datePhase).banks earlyFloor)
  pointerBank ((dateCalendar).memory sliceEnd censusBase replayRoom ((datePhase).memory earlyFloor (earlyImage readImage)))
local notation "packetHome" => Branch.publicHost X G S b positive base width
local notation "packetCounts" => Computability.BorderVNP.FragmentBucket.count (Branch.cohortHome X G S b positive base)
local notation "packetSize" => E₀*2^(j+rest)
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192


private theorem measured_packets_of_dated_reads (bins : W=NativeBranch.binLimit («k»:=k) S)
    (readMem : Memory w) (sameMem : readMem=datedMem) (kept : j≤S.groupWidth k tail S.length+k)
    (homesRead : ∀i:Fin packetSize,(dateHomes).read (packetPost readMem) (i.val:Computability.VPVNP.BurstRAM.Word w)=((packetHome i).val:Computability.VPVNP.BurstRAM.Word w))
    (countRead : ∀i:Fin H₀,(packetPrimitive readMem) (((dateSpec).census censusBase).base+i.val)=(packetCounts i:Computability.VPVNP.BurstRAM.Word w))
    (rosterRead : ∀i:Fin H₀,((packetPrimitive readMem) (((dateSpec).frozenRoster censusBase).base+i.val)).val=
      Branch.frozenRosterCode X G S b positive base i) : paidPackets_ := by
  subst readMem

  have samePost : postEntry_ = postBook pre :=
    @native_post_early_wide_books F _ cp P X G S k cut tail n h C f g W q piece ordinary reset j rest base headerRows paidRows
      w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress
      rosterBank datedFloor replayBase matrixTable dateTag dateRotation snapshots roleBase datedMem replayRoom bins
  refine ⟨kept,?_,?_,?_⟩
  ·
    intro i
    exact (congrArg (fun m₀ : Memory w => (dateHomes).read m₀ (i.val:Computability.VPVNP.BurstRAM.Word w)) samePost).symm.trans (homesRead i)
  ·
    exact countRead
  ·
    exact rosterRead

set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
local notation "selectedSites" => datedRowsChecked lookupBase dateHomes bookImage_ ownsRoster
  (fun _:Prop=>True) (fun _:Prop=>True) (fun _:Prop=>True)
local notation "selectedMatrix" => primitiveImage_ matrixFloor =
  ((DescentExterior.matrixCode (Branch.pinSpine X G S b positive base).matrix).val : Computability.VPVNP.BurstRAM.Word w)


private theorem physical_packet_and_matrix_from_reset
    (bins : W = NativeBranch.binLimit («k»:=k) S)
    (shopCount : (dateSpec).scalar.shops = (dateHardware).hosts)
    (alive : 0 < (dateSpec).scalar.shops)
    (priorMetadata : (dateOut).metadataEnd dateOrigin ≤ earlyFloor)
    (one : chunks (dateHardware).groups (dateHardware).lanes = 1)
    (roleEnd : roleBase+DescentTerminalRoleTables.count roleBankBits ≤ (dateSpec).cohortEnd censusBase)
    (layout : (dateSpec).Before censusBase paidBank actorBank wingBank peerBank (lookupPage).total (lookupPage).modulo dateHomes (lookupPage).boundaries)
    (paidRowsFit : ∀ x,(dateSpec).scalar.shops ≤ (paidBank x).size)
    (signedRows : ∀ x i,(dateSpec).scalar.shops ≤ (wingBank x i).size)
    (rankDirectory : ℕ → Bank) (rankShape : snapshots = Chronology.SnapshotCalendar reset
      (Chronology.kindCalendar S.rounds S.height) (capCalendar G.b S.rounds g S.height) rankDirectory)
    (priorMemory : Memory w) (rankFloor capture countRows : ℕ) (source : ℕ → ℕ)
    (roleMount : Chronology.RoleMount w roleBase replayBase)
    (memoryEq : datedMem = roleMount.phase.image (DescentLowCountBook.output capture source priorMemory countRows))
    (archived : (b).path.snapshotRanks snapshots rankFloor priorMemory)
    (rankFloorBound : rankFloor ≤ replayBase) (rankRole : rankFloor ≤ roleBase)
    (rankAway : ∀i < S.length, ∀bank,snapshots.compact i = some bank →
      bank.base+bank.size ≤ capture ∨ capture+countRows ≤ bank.base)
    (rotations : (b).path.RotationWords dateTag dateRotation datedMem)
    (addressRoom : (dateSpec).maskBase censusBase < 2^w) (wordPositive : 0 < w)
    (rotHi : ∀i < S.length,dateRotation i < replayBase)
    (below : matrixTable+32*DescentExteriorShelf.span j rest s E₀ ≤ replayBase)
    (retainedWidth : j ≤ S.groupWidth k tail S.length+k)
    (replayPayload : (k*S.length+1)*2^(8+S.capGain*S.length) ≤ w)
    : paidPackets_ ∧ selectedMatrix := by
  have replayRotations : (b).path.RotationWords dateTag dateRotation
      (roleMount.phase.image (DescentLowCountBook.output capture source priorMemory countRows)) :=
    memoryEq ▸ rotations
  have observations := issued_terminal_snapshot_labels (X:=X) (G:=G) (S:=S) (ordinary:=ordinary)
    (reset:=reset) (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten)
    (c:=c) snapshots rankDirectory rankShape
  have packets := Branch.scheduled_packet_homes (F:=F) (cp:=cp) (ar:=P) («k»:=k) («tail»:=tail)
    X G S base ordinary.radix g p q R rot
    headerRows paidRows j rest s replayBase matrixTable dateTag dateRotation datePhase snapshots blockCast shopCount
    roleBase peerBank paidBank actorBank wingBank replayRoom addressRoom wordPositive alive rotHi below
    priorMetadata one roleEnd layout paidRowsFit signedRows b positive width priorMemory
    rankFloor capture countRows source roleMount archived rankFloorBound rankRole rankAway
    observations.1 observations.2 retainedWidth replayPayload
  have packetData : paidPackets_ := by
    exact @measured_packets_of_dated_reads
      F _ cp P X G S k cut
      tail n h C f g W q piece
      ordinary reset branch positive room shorten c j rest
      base width headerRows paidRows w boardDegree board dateAge dateDegree
      datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase
      matrixTable dateTag dateRotation snapshots roleBase datedMem replayRoom
      bins _ memoryEq.symm retainedWidth packets.1 packets.2.2.1 packets.2.2.2
  have matrixData : selectedMatrix := by
    let readMatrix (inputMemory : Memory w) : Computability.VPVNP.BurstRAM.Word w :=
      (@nativePrimitive F _ cp P X G S k cut tail n h C f g W q piece reset
        j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload
        ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank
        datedFloor replayBase matrixTable dateTag dateRotation snapshots roleBase
        inputMemory replayRoom) matrixFloor
    have scheduledRead := Branch.scheduled_primitive_matrix
      (F:=F) (cp:=cp) (ar:=P) (k:=k) (tail:=tail)
      X G S base ordinary.radix g p q R rot headerRows paidRows
      j rest s replayBase matrixTable dateTag dateRotation datePhase snapshots blockCast shopCount
      roleBase peerBank paidBank actorBank wingBank replayRoom addressRoom wordPositive alive rotHi below
      priorMetadata one roleEnd layout paidRowsFit signedRows b positive priorMemory
      rankFloor capture countRows source roleMount archived rankFloorBound rankRole rankAway replayRotations
    exact (congrArg readMatrix memoryEq).trans scheduledRead
  exact ⟨packetData, matrixData⟩


private theorem earned_packet_publication_from_reset
    (bins : W = NativeBranch.binLimit («k»:=k) S)
    (shopCount : (dateSpec).scalar.shops = (dateHardware).hosts)
    (alive : 0 < (dateSpec).scalar.shops)
    (priorMetadata : (dateOut).metadataEnd dateOrigin ≤ earlyFloor)
    (one : chunks (dateHardware).groups (dateHardware).lanes = 1)
    (roleEnd : roleBase+DescentTerminalRoleTables.count roleBankBits ≤ (dateSpec).cohortEnd censusBase)
    (layout : (dateSpec).Before censusBase paidBank actorBank wingBank peerBank (lookupPage).total (lookupPage).modulo dateHomes (lookupPage).boundaries)
    (paidRowsFit : ∀ x,(dateSpec).scalar.shops ≤ (paidBank x).size)
    (signedRows : ∀ x i,(dateSpec).scalar.shops ≤ (wingBank x i).size)
    (rankDirectory : ℕ → Bank) (rankShape : snapshots = Chronology.SnapshotCalendar reset
      (Chronology.kindCalendar S.rounds S.height) (capCalendar G.b S.rounds g S.height) rankDirectory)
    (priorMemory : Memory w) (rankFloor capture countRows : ℕ) (source : ℕ → ℕ)
    (roleMount : Chronology.RoleMount w roleBase replayBase)
    (memoryEq : datedMem = roleMount.phase.image (DescentLowCountBook.output capture source priorMemory countRows))
    (archived : (b).path.snapshotRanks snapshots rankFloor priorMemory)
    (rankFloorBound : rankFloor ≤ replayBase) (rankRole : rankFloor ≤ roleBase)
    (rankAway : ∀i < S.length, ∀bank,snapshots.compact i = some bank →
      bank.base+bank.size ≤ capture ∨ capture+countRows ≤ bank.base)
    (rotations : (b).path.RotationWords dateTag dateRotation datedMem)
    (addressRoom : (dateSpec).maskBase censusBase < 2^w) (wordPositive : 0 < w)
    (rotHi : ∀i < S.length,dateRotation i < replayBase)
    (below : matrixTable+32*DescentExteriorShelf.span j rest s E₀ ≤ replayBase)
    (retainedWidth : j ≤ S.groupWidth k tail S.length+k)
    (replayPayload : (k*S.length+1)*2^(8+S.capGain*S.length) ≤ w)
    (actual : physicalRows trueRoster) (captured : paidCapture_)
    (earned : paidPackets_ → selectedMatrix → selectedSites) :
    publishedAt_ lookupBase dateHomes bookImage_ := by
  have receipts : paidPackets_ ∧ selectedMatrix :=
    @physical_packet_and_matrix_from_reset
      F _ cp P X G S k cut tail
      n h C f g W q piece ordinary reset
      branch positive room shorten c j rest base width headerRows
      paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes
      previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateTag dateRotation snapshots roleBase
      datedMem replayRoom bins shopCount alive priorMetadata one roleEnd layout paidRowsFit
      signedRows rankDirectory rankShape priorMemory rankFloor capture countRows source roleMount memoryEq
      archived rankFloorBound rankRole rankAway rotations addressRoom wordPositive rotHi below retainedWidth
      replayPayload
  have sitesAt : selectedSites := earned receipts.1 receipts.2
  have rowsAt : inputsAt_ lookupBase dateHomes bookImage_ :=
    @wide_earned_from_registered
      F _ cp P X G S k cut tail
      n h C f g W q piece ordinary reset
      branch positive room shorten c j rest base width age
      wFit qFit qh template sitesPositive rawWords headerRows paidRows pool raw
      w K payloadBits fit rom other arity groups stride oldTags
      codec lo packWidth all head short fence count plan original
      boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress
      rosterBank datedFloor replayBase matrixTable dateTag dateRotation snapshots roleBase datedMem dateInput
      replayRoom actual captured receipts.1 sitesAt
  exact @wide_earned_primitive_sources
      F _ cp P X G S k cut tail
      n h C f g W q piece ordinary reset
      branch positive room shorten c j rest base width age
      wFit qFit qh template sitesPositive rawWords headerRows paidRows pool raw
      w K payloadBits fit rom other arity groups stride oldTags
      codec lo packWidth all head short fence count plan original
      boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress
      rosterBank datedFloor replayBase matrixTable dateTag dateRotation snapshots roleBase datedMem dateInput
      replayRoom rowsAt

end
end Hierarchy.DescentSixParty.SeedNamed

namespace Hierarchy.DescentSixParty.SeedNamed
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM.PhysicalProcedure ProtocolRAM
open DescentStaticWordColumn

private theorem combine_census_program_counts {w : ℕ}
    (prefixProgram bootProgram historyProgram terminalProgram relocateProgram planProgram voteProgram
      clockProgram chipProgram trailingProgram : Procedure w)
    (prefixTicks bootTicks historyTicks terminalTicks relocateTicks planTicks voteTicks
      clockTicks chipTicks trailingTicks rawCount bins slots : ℕ)
    (tailBill : trailingTicks + 7 * names trailingProgram ≤ 4169 + 100*rawCount + 6*bins + 300*slots) :
    let middle := (bootProgram.seq historyProgram).seq terminalProgram
    let reel := ((historyProgram.seq terminalProgram).seq relocateProgram).seq planProgram
    let issued := (((((prefixProgram.seq (middle.seq relocateProgram)).seq planProgram).seq voteProgram).seq clockProgram).seq chipProgram).seq trailingProgram
    let consumed := (((prefixTicks + ((bootTicks+historyTicks+terminalTicks)+relocateTicks))+planTicks)
      + voteTicks + clockTicks) + chipTicks + trailingTicks + 3
    (issued.labels+3)+(issued.registers+1)+consumed ≤
      (prefixTicks+bootTicks+7*(names prefixProgram+names bootProgram)) +
      (historyTicks+terminalTicks+relocateTicks+planTicks+7*names reel) +
      (voteTicks+7*names voteProgram) + (clockTicks+chipTicks+7*(names clockProgram+names chipProgram)) +
      4176 + 100*rawCount + 6*bins + 300*slots := by
  intro middle reel issued consumed
  have hardware : issued.labels+issued.registers ≤ names issued := Nat.le_add_right ..
  simp only [issued, middle, names_seq] at hardware
  simp only [consumed, reel, names_seq]
  change (issued.labels+3)+(issued.registers+1)+_≤_
  change issued.labels+issued.registers ≤ _ at hardware
  omega

private theorem combine_four_stage_charges
    (h w rate T fund sites cells pinCount outside firstFree boot reel verdict finish pcs regs fuel
       raw width bins slots price sourceRate bootRate reelRate verdictRate endRate : ℕ)
    (bus:w≤rate*h) (live:0<sites) (ambient:2^h≤ sites) (mode:width≤h+1) (alphabet:bins≤ sites)
    (seed:((cells+pinCount+outside)+firstFree*(h+1))*T≤ sourceRate*fund)
    (paidBoot:boot*(h+1)*T≤bootRate*fund) (paidReel:reel*(h+1)*T≤reelRate*fund)
    (paidVerdict:verdict*(h+1)*T≤verdictRate*fund) (paidEnd:finish*(h+1)*T≤endRate*fund)
    (inventory:sites*(h+1)*T≤64*fund) (rawPaid:raw≤firstFree) (poolPaid:slots≤finish)
    (hardware:pcs+regs+fuel≤boot+reel+verdict+finish+4176+100*raw+6*bins+300*slots) :
    (cells+9*(raw*width)+(1+bins+1)*(w+1)+pinCount+outside+
      price*(pcs+regs+firstFree+fuel+(raw+(1+bins+1))+2^h+1)*(h+1))*T ≤
      earnedHostPrice sourceRate sourceRate (bootRate+reelRate+verdictRate+endRate) rate price * fund := by
  have original : (boot+reel+verdict+finish)*(h+1)*T≤(bootRate+reelRate+verdictRate+endRate)*fund := by
    simpa only [Nat.add_mul] using Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add paidBoot paidReel) paidVerdict) paidEnd
  have seedPaid:(cells+pinCount+outside)*T≤ sourceRate*fund :=
    (Nat.mul_le_mul_right T (Nat.le_add_right ..)).trans seed
  have inputPaid:firstFree*(h+1)*T≤ sourceRate*fund :=
    (Nat.mul_le_mul_right T (Nat.le_add_left ..)).trans seed
  have total : slots ≤ boot+reel+verdict+finish := poolPaid.trans (Nat.le_add_left ..)
  have result := earned_host_invoice h w rate T fund sites (cells+pinCount+outside) firstFree
    (boot+reel+verdict+finish) pcs regs fuel (raw+(1+bins+1)) raw width bins slots price
    sourceRate sourceRate (bootRate+reelRate+verdictRate+endRate) mode bus live ambient seedPaid
    inputPaid original inventory rawPaid alphabet total rfl hardware
  simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using result

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
set_option maxRecDepth 12288
set_option maxHeartbeats 1400000
set_option cleanup.letToHave false
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin Branch.archive Branch.bundleShape

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g W q piece : ℕ}
local notation "p" => W*piece
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0<(W*piece)) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
local notation "s" => S.firstWidth G.b p
local notation "Z" => S.grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "cap" => NativeBranch.privateSlotCapacity G S R
local notation "nodeCap" => S.epochPower^S.localTokenExponent
local notation "venues" => S.groupCount S.length*2^k

variable {j rest : ℕ} (base : S.baseGroups=2^tail) (width : S.groupWidth k tail 0+k=j+(j+rest))
variable (age : 0<S.height) (wFit : NativeBranch.binLimit (k:=k) S ≤ W)
  (qFit : NativeBranch.localLimit G S ≤ q) (qh : 0<q)

open DescentExterior Computability.VPVNP.RAMSerialization DescentTerminalExteriorPackets DescentTerminalPublicIdentity
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall DescentPackedProfileTape
open DescentSeedRoot DescentExteriorShelf DescentTerminalPrimitiveArena
local notation "E₀" => Fintype.card (Port P X.width)
local notation "H₀" => S.hostSize S.length
local notation "count₀" => E₀*2^(j+rest)
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
local instance wideEarnedStageChartFinite : Fintype (chart).Pin := (chart).finite
local notation "fmt" => Branch.geometryFormat G S k g p tail q R rot headerRows paidRows
local notation "pre" => Branch.preflightSpec X G S k g p tail ({fmt with binSize:=W}:Branch.PreflightFormat)
variable (lo packWidth : ℕ)
local notation "steps" => (chart).layout
local notation "matrixAt" => end_ (lo+extent packWidth steps) G.C packWidth
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentResetInvoice CorrectionBatch
open DescentSixParty.SeedNamed.Branch DescentExteriorReplay DescentTerminalFixedSlices
open DescentTerminalPointerDigits DescentTerminalCombinedRole DescentSIMDLookup DescentPackedColony
open ThreeFlat.Routing CallPool DescentColonies DescentActorRaster DescentColonies.SplitRAM
open DescentTerminalRoleTables DescentTerminalPointerIssue
variable {boardDegree:ℕ} (board : NonlinearExpanders.Graph n boardDegree) (dateAge dateDegree datePayload : ℕ)
    (ordinaryAt : ℕ→Dated.Ordinary) (operandLanes primitiveLanes : ℕ) (previousDate : StageVenueTail.Date)
    (priorAddress : ℕ→ℕ→Bank) (rosterBank : Bank) (datedFloor replayBase : ℕ)
    (dateTag : ℕ→Bool) (dateRotation : ℕ→ℕ) (snapshots : Snapshots k) (roleBase : ℕ)

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
variable (replayRoom : ((replayCalendar X S k tail j rest snapshots)).stop (((((preflightSpec X G S k g (W*piece) tail (geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows))).scanPages (((replayCalendar X S k tail j rest snapshots)).packetEnd (((Phase.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset)   operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).stop (DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail replayBase j rest (S.firstWidth G.b (W*piece)) (Fintype.card (Port P X.width))))) q)).stop)<2^w)
local notation "dateEntryAt" mu:arg => (dateCalendar).memory sliceEnd censusBase replayRoom ((datePhase).memory earlyFloor (earlyImage mu))
local notation "primitiveOf" mu:arg => (dateSpec).primitiveSnapshot (base:=censusBase) (w:=w) (q:=q) («p»:=p) (nd:=atomBits)
  (nodes:=nodeCap) (hidden:=cap) (args:=cap) (oldPaid:=paidBank) (actor:=actorBank) (first:=roleBanks) (second:=arityBanks)
  («chart»:=operandChart) (f0:=publicCell) (f7:=privateCell) ((lookupPage).image (dateEntryAt mu))
local notation "datedDecoder" => Branch.decodeBook S G base ordinary.radix p q 3
  (dateSpec).cap (dateSpec).printBits (by decide)
local notation "booksOf" mu:arg => (dateSpec).bookSnapshot (base:=censusBase) («peer»:=peerBank) (wing:=wingBank)
  (w:=w) (q:=q) («p»:=p) (nd:=atomBits) (nodes:=nodeCap) (hidden:=cap) (args:=cap)
  (oldPaid:=paidBank) (actor:=actorBank) (first:=roleBanks) (second:=arityBanks) («chart»:=operandChart)
  (f0:=publicCell) (f7:=privateCell) (decode:=datedDecoder) ((lookupPage).image (dateEntryAt mu))
local notation "dateHomes" => (dateCalendar).homes sliceEnd

local notation "begin_" => censusBase
local notation "peer" => peerBank
local notation "old" => wingBank
local notation "org" => lookupBase
local notation "homes" => dateHomes
variable (rom : ℕ) (other:AddressPlan.Input)
local notation "arity" => max 8 (2^S.capGain)
local notation "groups" => cap
local notation "stride" => R
local notation "oldTags" => DescentPrimitivePalette.colors G s Z rot
local notation "codec" => DescentPrimitivePalette.codec (G:=G) («s»:=s) («Z»:=Z) rot
local notation "tagCount" => DescentBundleTagKeys.capacity oldTags arity groups p stride
local notation "V" => (⟨q,tagCount,cap,nodeCap,cap,p,groupsAt⟩:Home.Format)
local notation "pages₀" => (pre).scanPages org q
local notation "total" => (pages₀).total
local notation "modulo" => (pages₀).modulo
local notation "boundary" => (pages₀).boundaries
local notation "routeTables" => (RouteSources.Tables.mk 4 venues (venues*NativeBranch.localLimit G S)
  (NativeBranch.localLimit G S) (Book.tokenBits (venues*NativeBranch.localLimit G S)) W q K)
local notation "B" => (pre).pageBits
local notation "grain" => p
local notation "codes" => DescentTerminalScalarHeader.range q tagCount cap nodeCap cap p venues
local notation "seed" => (chart).seed
local notation "clockCap" => G.C
local notation "front" => end_ (lo+extent packWidth steps) clockCap packWidth+17*DescentExteriorShelf.span j rest s E₀
local notation "extra" => DescentTerminalPublicIdentity.total K W q piece codes rawWords count₀
local notation "Full" => DescentTerminalFullPins.Candidate ((chart).Pin⊕Hidden E₀ j rest s) K W q piece rawWords
local notation "power" => NativeBranch.copy_power S (radix:=ordinary.radix) base width
local notation "I_" => (pre).reachedInput begin_ rom q piece W K codes front peer old total modulo homes
                          boundary cfg V other routeTables (pre).vertices B
local notation "R_" => (pre).channels begin_
local notation "start" => (pre).maskBase begin_
local notation "base_" => afterMeter V cfg R_ start
local notation "A_" => rowArena cfg I_ base_
local notation "J_" => (pre).chipInput begin_ rom q grain peer old total modulo homes boundary cfg other

variable (head : ℕ) (short : ((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).vertices*DescentTerminalVertexFields.span (((⟨q,(DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) ((NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))) (W*piece) ((max 1 (max reset.bitsR (C*reset.bitsR))))),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).publicArity (((⟨q,(DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) ((NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))) (W*piece) ((max 1 (max reset.bitsR (C*reset.bitsR))))),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).roles (((⟨q,(DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) ((NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))) (W*piece) ((max 1 (max reset.bitsR (C*reset.bitsR))))),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).privateWords (((⟨q,(DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) ((NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))) (W*piece) ((max 1 (max reset.bitsR (C*reset.bitsR))))),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).nodes (((⟨q,(DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) ((NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))) (W*piece) ((max 1 (max reset.bitsR (C*reset.bitsR))))),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).addresses (((⟨q,(DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) ((NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))) (W*piece) ((max 1 (max reset.bitsR (C*reset.bitsR))))),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).piece≤(((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).pageBits))
local notation "literal" => ScalarLiterals.data q (V).roles (V).privateWords (V).nodes (V).addresses grain (pre).vertices W B
  (cfg).terminal.pool qh ((routeTables).columns A_ (J_).sources) ((routeTables).value (fun _ _=>0))
local notation "O_" => registers V cfg R_ start head
local notation "plan_" => AddressPlan.layout cfg I_ base_ O_

local notation "emptyCode" => (DescentTerminalChronologicalBooks.empty q tagCount cap nodeCap cap p venues p).val
local notation "bankSet" => DescentTerminalChipBootWords.chipBanks (K:=K) (W:=W) (q:=q)
  («p»:=piece) codes (plan_).emit front emptyCode

local notation "wall" => AddressPlan.takeOff (cfg) I_ base_
local notation "compact" => end_ (lo+extent packWidth steps) G.C packWidth
local notation "firstFree" => front+extra
local notation "dst" => DescentPackedEpochShelves.finalAt firstFree lo packWidth steps
local notation "seedBase" => DescentWideSeedFlags.endInput X S.copies s payloadBits
local notation "seedRows" => DescentPackedSeed.rows X S.copies s payloadBits
local notation "B₀" => S.groupWidth k tail 0+k
open Chronology DescentDatedSeedStartup.Input DescentTerminalEpochDecoder DescentPackedSeed DescentExteriorShelf
variable {bootHosts:ℕ} (hostsEnough:Fintype.card (Vertex X)≤bootHosts) (startup:DescentDatedSeedStartup.Layout)
  (startingHeader:ℕ) (datesAt:ℕ→DateCode w) (capture:ℕ) (countAt:ℕ→ℕ)
variable (roleMount : Chronology.RoleMount w roleBase replayBase)
local notation "captureDates" => countDates 0 (kindCalendar S.rounds S.height)
local notation "rowAddress" => fun i:ℕ=>countAt ((captureDates)[i]?.getD 0)
local notation "oldReel" => DescentExteriorMatrixUpdate.Calendar.reel S k tail replayBase dateTag dateRotation
local notation "matrixEnd" => DescentExteriorMatrixUpdate.Calendar.stop S k tail replayBase
local notation "termCode" => Branch.postEarlyPreflight X G S base ordinary.radix g p q R rot headerRows paidRows
  j rest s replayBase datePhase snapshots blockCast roleBase peerBank paidBank actorBank wingBank replayRoom
local notation "termCost" => Branch.postEarlyPreflightClocks X G S (k:=k) (tail:=tail) g p q R rot headerRows paidRows
  j rest s replayBase datePhase snapshots blockCast peerBank paidBank actorBank wingBank replayRoom
local notation "bootCode" => completeAfter G rot X (S.initialDigits ordinary.radix) hostsEnough startup startingHeader payloadBits Z w
local notation "bootCost" => completeTicks (S:=S) (k:=k) G rot X hostsEnough startup payloadBits Z w
local notation "originalMid" => ((DateCode.afterBoot bootCode datesAt S.length).seq
   (Branch.historyMountedReel X S replayBase dateTag dateRotation countAt capture matrixAt k tail j rest s w roleMount.phase)).seq termCode
local notation "originalCost" => (DateCode.afterTicks bootCost datesAt S.length+
    (((4+11*(captureDates).length)+roleMount.phase.ticks)+DescentExteriorMatrixUpdate.Calendar.earlyClock S k tail j rest s datePorts))+termCost
local notation "upperFence" => (pre).maskBase censusBase
local notation "freshReel" => DescentExteriorMatrixUpdate.Reel.late oldReel upperFence
local notation "countSlot" => fun i:ℕ=>capture+i
local notation "fence" => upperFence
local notation "count" => countSlot
local notation "plan" => freshReel

local notation "middle" => originalMid
local notation "cost" => originalCost
local notation "initialFlag" => seedBase+seedRows
local notation "foldSites" => DescentPackedEpochShelves.controlsAt firstFree lo G.C packWidth steps count (fun _=>initialFlag)
local notation "prefixCode" => DescentWideSeedFlags.check X S.copies s payloadBits w
local notation "paidCode" => (((((prefixCode).seq ((middle).seq (relocate j rest s E₀ w compact wall))).seq
    ((plan).program j rest s E₀ w B₀ S.length wall)).seq (fold w initialFlag dst foldSites)).seq
    (AddressPlan.clock V cfg I_ R_ start head short literal (bw:=w)))
local notation "paidTime" => ((4+(seedRows+1)*66+(cost+(4+18*(17*DescentExteriorShelf.span j rest s E₀))))+
    (10+((4+58*S.length)+(4+16*E₀))))+bill initialFlag dst foldSites+AddressPlan.time V cfg I_ R_ start head
local notation "charge" => fun v=> (normalizedLeaf X G S ordinary reset branch positive room shorten v
  base width age wFit qFit qh cfg pool raw).debt cfg

local notation "extPins" => Port ((S.copies*s)*P) (CorrectionFrame.copiesWidth (S.copies*s) X.width)
local notation "view" x₀:arg => Branch.copyInput X s power x₀
local notation "bootFor" x₀:arg z₀:arg => Root.appended front extra
    (Root.widePackedImage X S.copies s payloadBits w seed lo G.C packWidth steps compact
      (DescentExterior.publicRows X (view x₀)) (Sum.elim (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inl)
      (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inr)))
    (DescentTerminalPublicIdentity.back (z₀ ∘ DescentTerminalFullPins.chip) w codes count₀)

local notation "histAt" z₀:arg => (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inl)
local notation "checkedAt" x₀:arg z₀:arg => DescentWideSeedFlags.countedAt X S.copies s payloadBits seed
  (histAt z₀) (bootFor x₀ z₀)
local notation "startedAt" x₀:arg z₀:arg => completeImage G rot X (S.initialDigits ordinary.radix) hostsEnough startup
  startingHeader payloadBits Z (checkedAt x₀ z₀)
local notation "lastAt" x₀:arg z₀:arg => DateCode.history datesAt (startedAt x₀ z₀) S.length
local notation "capturedAt" x₀:arg z₀:arg => roleMount.phase.image (DescentLowCountBook.output capture rowAddress (lastAt x₀ z₀) (captureDates).length)
local notation "primitiveBank" => fun (x₀:extPins→Bool)(z₀:Full→Bool)=>primitiveOf (capturedAt x₀ z₀)
local notation "booksBank" => fun (x₀:extPins→Bool)(z₀:Full→Bool)=>booksOf (capturedAt x₀ z₀)
local notation "selectedAt" z₀:arg => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow (histAt z₀)
local notation "honestAt" z₀:arg => issued X G S ordinary reset branch positive room shorten (selectedAt z₀)
local notation "acceptAt" z₀:arg => ∃c,(chart).read (histAt z₀)=some c
local notation "layout_" => fun c=>Branch.publicLayout X G S (issued X G S ordinary reset branch positive room shorten c)
  positive base width
local notation "whichAt" x₀:arg z₀:arg => proposed (chart).read layout_ (DescentExterior.publicRows X (view x₀))
  (z₀ ∘ DescentTerminalFullPins.history)
variable (machine:sliceWidth W q piece≤w)

local notation "cols" => AddressPlan.observationColumns V cfg I_ R_ start head dst

local notation "candidatePrior" => wideChoicePrior X G S ordinary reset branch positive room shorten w fit base width
local notation "seedNet" => wideChoiceCircuit (K:=K) (W:=W) (q:=q) (piece:=piece) X G S ordinary reset branch positive room shorten w fit (j:=j) (rest:=rest) cfg
local notation "numBins" => DescentTerminalChronologicalBooks.Keys q tagCount cap nodeCap cap p venues p
local notation "numSlots" => (cfg).terminal.pool
local notation "cpu" => AddressPlan.chip cfg I_ base_
local notation "tapeDesc" => (cols).tape cpu (K*W)
local notation "widthWord" => q*p

local notation "countWidth_" => w+1
local notation "readoutEnd_" => AddressPlan.last V cfg I_ R_ start
local notation "cut_" => DescentTerminalLast.trailingCut readoutEnd_ (cfg).terminal.rows
local notation "stop_" => DescentTerminalLast.trailingStop cut_ rawWords numSlots numBins
variable (censusRoom : (DescentTerminalLast.trailingStop (DescentTerminalLast.trailingCut (AddressPlan.last ((⟨q,(DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) ((NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))) (W*piece) ((max 1 (max reset.bitsR (C*reset.bitsR))))),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format)) (Branch.exteriorShape template (Fintype.card (Port P X.width)) j rest (S.firstWidth G.b (W*piece)) rawWords headerRows (S.hostSize S.length) sitesPositive) (((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).reachedInput ((((((preflightSpec X G S k g (W*piece) tail (geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows))).scanPages (((replayCalendar X S k tail j rest snapshots)).packetEnd (((Phase.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset)   operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).stop (DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail replayBase j rest (S.firstWidth G.b (W*piece)) (Fintype.card (Port P X.width))))) q)).stop)) rom q piece W K (DescentTerminalScalarHeader.range q (DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) ((NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))) (W*piece) ((max 1 (max reset.bitsR (C*reset.bitsR))))) (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))) (S.epochPower^S.localTokenExponent) (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))) (W*piece) (S.groupCount S.length*2^k)) (end_ (lo+extent packWidth (((normalizedPackedChart X G S ordinary reset branch positive room shorten w fit)).layout)) (G.C) packWidth+17*DescentExteriorShelf.span j rest (S.firstWidth G.b (W*piece)) (Fintype.card (Port P X.width))) ((((((Phase.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset)   operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).output)).terminalPeer (((Phase.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset)   operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).dateBase))) ((fun (x:Fin (((preflightSpec X G S k g (W*piece) tail (geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows))).scalar.blocks)) (a:Fin (2*((preflightSpec X G S k g (W*piece) tail (geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows))).cap))=>((((Phase.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset)   operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).output)).terminalWing (((Phase.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset)   operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).dateBase) x.val a.val)) (((((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).scanPages ((((replayCalendar X S k tail j rest snapshots)).packetEnd (((Phase.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset)   operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).stop (DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail replayBase j rest (S.firstWidth G.b (W*piece)) (Fintype.card (Port P X.width)))))) q)).total) (((((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).scanPages ((((replayCalendar X S k tail j rest snapshots)).packetEnd (((Phase.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset)   operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).stop (DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail replayBase j rest (S.firstWidth G.b (W*piece)) (Fintype.card (Port P X.width)))))) q)).modulo) ((((replayCalendar X S k tail j rest snapshots)).homes (((Phase.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset)   operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).stop (DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail replayBase j rest (S.firstWidth G.b (W*piece)) (Fintype.card (Port P X.width))))))                           (((((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).scanPages ((((replayCalendar X S k tail j rest snapshots)).packetEnd (((Phase.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset)   operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).stop (DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail replayBase j rest (S.firstWidth G.b (W*piece)) (Fintype.card (Port P X.width)))))) q)).boundaries) (Branch.exteriorShape template (Fintype.card (Port P X.width)) j rest (S.firstWidth G.b (W*piece)) rawWords headerRows (S.hostSize S.length) sitesPositive) ((⟨q,(DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) ((NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))) (W*piece) ((max 1 (max reset.bitsR (C*reset.bitsR))))),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format)) other ((RouteSources.Tables.mk 4 (S.groupCount S.length*2^k) ((S.groupCount S.length*2^k)*NativeBranch.localLimit G S)   (NativeBranch.localLimit G S) (Book.tokenBits ((S.groupCount S.length*2^k)*NativeBranch.localLimit G S)) W q K)) ((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).vertices (((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).pageBits)) (((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).channels ((((((preflightSpec X G S k g (W*piece) tail (geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows))).scanPages (((replayCalendar X S k tail j rest snapshots)).packetEnd (((Phase.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset)   operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).stop (DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail replayBase j rest (S.firstWidth G.b (W*piece)) (Fintype.card (Port P X.width))))) q)).stop))) (((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).maskBase ((((((preflightSpec X G S k g (W*piece) tail (geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows))).scanPages (((replayCalendar X S k tail j rest snapshots)).packetEnd (((Phase.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset)   operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).stop (DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail replayBase j rest (S.firstWidth G.b (W*piece)) (Fintype.card (Port P X.width))))) q)).stop)))) ((Branch.exteriorShape template (Fintype.card (Port P X.width)) j rest (S.firstWidth G.b (W*piece)) rawWords headerRows (S.hostSize S.length) sitesPositive)).terminal.rows) rawWords (((Branch.exteriorShape template (Fintype.card (Port P X.width)) j rest (S.firstWidth G.b (W*piece)) rawWords headerRows (S.hostSize S.length) sitesPositive)).terminal.pool) (DescentTerminalChronologicalBooks.Keys q (DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) ((NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))) (W*piece) ((max 1 (max reset.bitsR (C*reset.bitsR))))) (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))) (S.epochPower^S.localTokenExponent) (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))) (W*piece) (S.groupCount S.length*2^k) (W*piece)))+1<2^w)
local notation "banks_" => DescentTerminalLast.trailingBanks w numSlots numBins cut_ rawWords
  (Nat.lt_trans (Nat.lt_succ_self _) censusRoom)
local notation "fed" => (paidCode).seq (DescentTerminalChipRuntime.program cpu bankSet w (K*W) numSlots)
local notation "whole" => DescentTerminalReadout.complete tapeDesc banks_ (cut:=cut_) (stop:=stop_) (rows:=rawWords) (word:=widthWord) fed
local notation "pcs" => (whole).labels+3
local notation "regs" => (whole).registers+1
local notation "binsPaid" => Fintype.card Unit+numBins+1
local notation "obs" => rawWords+binsPaid
local notation "fuel" => paidTime+clocks (K*W) numSlots+ticks tapeDesc banks_ rawWords widthWord+3
local notation "runtime" => CheapISA.hostFuel fuel

/-- Allocated last address and native execution bill of the trailing census on this
original paid terminal tape. -/
theorem wide_census_invoice :
    stop_+1≤readoutEnd_+2*(cfg).terminal.rows+rawWords+4*numSlots+numBins+2 ∧
    ticks tapeDesc banks_ rawWords widthWord+
      7*DescentStaticWordColumn.names (DescentTerminalLast.program tapeDesc banks_ cut_ stop_ rawWords widthWord)≤
        4169+100*rawWords+6*numBins+300*numSlots :=
  ⟨DescentTerminalLast.trailing_end_bound ..,
    DescentTerminalLast.trailing_invoice tapeDesc banks_ cut_ stop_ rawWords widthWord⟩

local notation "bootWork_" => 4+(seedRows+1)*66+DateCode.afterTicks bootCost datesAt S.length+
  7*(DescentStaticWordColumn.names prefixCode+
     DescentStaticWordColumn.names (DateCode.afterBoot bootCode datesAt S.length))
local notation "reelCode_" => (((Branch.historyMountedReel X S replayBase dateTag dateRotation countAt capture matrixAt k tail j rest s w roleMount.phase).seq
  termCode).seq (relocate j rest s E₀ w compact wall)).seq ((plan).program j rest s E₀ w B₀ S.length wall)
local notation "reelWork_" => (((4+11*(captureDates).length)+roleMount.phase.ticks)+DescentExteriorMatrixUpdate.Calendar.earlyClock S k tail j rest s datePorts)+
  termCost+(4+18*(17*DescentExteriorShelf.span j rest s E₀))+(10+((4+58*S.length)+(4+16*E₀)))+
  7*DescentStaticWordColumn.names reelCode_
local notation "voteWork_" => bill initialFlag dst foldSites+7*DescentStaticWordColumn.names (fold w initialFlag dst foldSites)
local notation "endWork_" => AddressPlan.time V cfg I_ R_ start head+clocks (K*W) numSlots+
  7*(DescentStaticWordColumn.names (AddressPlan.clock V cfg I_ R_ start head short literal (bw:=w))+
    DescentStaticWordColumn.names (DescentTerminalChipRuntime.program cpu bankSet w (K*W) numSlots))
local notation "allWork_" => bootWork_+reelWork_+voteWork_+endWork_
local notation "gates_" => 4*((seedNet).cells+(seedNet).internal)+Fintype.card Full+Fintype.card extPins
local notation "isa_" r:arg => 257*(1000*(2*(7*(r+6))+2)*(2*4^7+1))+256*fixedISAPrice*(r+6)

set_option maxHeartbeats 3500000 in
/-- The issued program has exactly the original paid phases, followed by the
three trailing scans of the residue, histogram and cutoff. -/
theorem wide_earned_native_count :
    pcs+regs+fuel≤allWork_+4176+100*rawWords+6*numBins+300*numSlots :=by
  exact combine_census_program_counts
    prefixCode (DateCode.afterBoot bootCode datesAt S.length)
    (Branch.historyMountedReel X S replayBase dateTag dateRotation countAt capture matrixAt k tail j rest s w roleMount.phase)
    termCode (relocate j rest s E₀ w compact wall) ((plan).program j rest s E₀ w B₀ S.length wall)
    (fold w initialFlag dst foldSites) (AddressPlan.clock V cfg I_ R_ start head short literal (bw:=w))
    (DescentTerminalChipRuntime.program cpu bankSet w (K*W) numSlots)
    (DescentTerminalLast.program tapeDesc banks_ cut_ stop_ rawWords widthWord)
    (4+(seedRows+1)*66) (DateCode.afterTicks bootCost datesAt S.length)
    (((4+11*(captureDates).length)+roleMount.phase.ticks)+DescentExteriorMatrixUpdate.Calendar.earlyClock S k tail j rest s datePorts)
    termCost (4+18*(17*DescentExteriorShelf.span j rest s E₀)) (10+((4+58*S.length)+(4+16*E₀)))
    (bill initialFlag dst foldSites) (AddressPlan.time V cfg I_ R_ start head) (clocks (K*W) numSlots)
    (ticks tapeDesc banks_ rawWords widthWord) rawWords numBins numSlots
    (DescentTerminalLast.trailing_invoice tapeDesc banks_ cut_ stop_ rawWords widthWord)


set_option maxHeartbeats 6000000 in
/-- These receipts are for independent native programs. The endgame receipt
also covers the final histogram pool by the number of actual chip writes. -/
theorem wide_earned_native_bill (ratio T sites sourceRate bootRate reelRate verdictRate endRate:ℕ)
    (bus:w≤ratio*payloadBits) (positiveSites:0<sites) (ambient:2^payloadBits≤ sites)
    (mode:widthWord≤payloadBits+1) (alphabet:numBins≤ sites)
    (boughtSeed:(gates_+firstFree*(payloadBits+1))*T≤ sourceRate*((S.copies*s)*(sites+T*E₀)))
    (boughtBoot:bootWork_*(payloadBits+1)*T≤bootRate*((S.copies*s)*(sites+T*E₀)))
    (boughtReel:reelWork_*(payloadBits+1)*T≤reelRate*((S.copies*s)*(sites+T*E₀)))
    (boughtVerdict:voteWork_*(payloadBits+1)*T≤verdictRate*((S.copies*s)*(sites+T*E₀)))
    (boughtEnd:endWork_*(payloadBits+1)*T≤endRate*((S.copies*s)*(sites+T*E₀)))
    (inventory:sites*(payloadBits+1)*T≤64*((S.copies*s)*(sites+T*E₀))) :
    (4*((seedNet).cells+(seedNet).internal)+9*(rawWords*widthWord)+binsPaid*countWidth_+
      Fintype.card Full+Fintype.card extPins+
      (isa_ ratio)*(pcs+regs+firstFree+fuel+obs+2^payloadBits+1)*(payloadBits+1))*T≤
    earnedHostPrice sourceRate sourceRate (bootRate+reelRate+verdictRate+endRate) ratio (isa_ ratio)*
      ((S.copies*s)*(sites+T*E₀)) :=by
  have originalRows : rawWords ≤ firstFree :=
    (AddressPlan.paid_columns K W q piece codes rawWords count₀).1.trans (Nat.le_add_left ..)
  have poolTicks : numSlots ≤ clocks (K*W) numSlots := by
    unfold DescentTerminalChipRuntime.clocks
    omega
  have poolFinish : numSlots ≤ endWork_ :=
    (poolTicks.trans (Nat.le_add_left ..)).trans (Nat.le_add_right ..)
  exact combine_four_stage_charges payloadBits w ratio T ((S.copies*s)*(sites+T*E₀)) sites
    (4*((seedNet).cells+(seedNet).internal)) (Fintype.card Full) (Fintype.card extPins)
    firstFree bootWork_ reelWork_ voteWork_ endWork_ pcs regs fuel rawWords widthWord numBins numSlots
    (isa_ ratio) sourceRate bootRate reelRate verdictRate endRate bus positiveSites ambient mode alphabet
    boughtSeed boughtBoot boughtReel boughtVerdict boughtEnd inventory originalRows poolFinish
    (@wide_earned_native_count F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch
      positive room shorten j rest base qh template sitesPositive rawWords headerRows paidRows w K
      payloadBits fit lo packWidth boardDegree board dateAge dateDegree datePayload ordinaryAt
      operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase dateTag
      dateRotation snapshots roleBase replayRoom rom other head short bootHosts hostsEnough startup
      startingHeader datesAt capture countAt roleMount censusRoom)



/-- The literal paid boot contains the header alphabet, all possible data
words, and the raw observation rows. It lies below the attained readout. -/
theorem wide_earned_census_room (L:ℕ) (live:0<payloadBits)
    (reelAbove:dst<DescentExteriorMatrixUpdate.Calendar.earlyAt S k tail replayBase)
    (readout:readoutEnd_≤2^(L*payloadBits)) (bus:(2*L+7)*payloadBits≤w) : stop_+1<2^w :=by
  have firstToVote : firstFree≤dst:=Nat.le_add_right ..
  have reelToEnd : DescentExteriorMatrixUpdate.Calendar.earlyAt S k tail replayBase≤earlyFloor :=
    Nat.le_add_right ..
  have low : earlyFloor ≤ sliceEnd := by
    change earlyFloor ≤ earlyFloor + _ + _ + _
    exact ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  obtain ⟨firstStep, snapshotStep, packetStep, _, _⟩ := (dateCalendar).addresses sliceEnd censusBase
  have lookupBound : lookupBase ≤ censusBase := Nat.le_add_right ..
  have replayed : earlyFloor ≤ censusBase :=
    low.trans (firstStep.trans (snapshotStep.trans (packetStep.trans lookupBound)))
  have begun : censusBase ≤ start := by
    rw [(pre).section_end censusBase]
    exact Nat.le_add_right ..
  have prefixRoom : extra≤ start := (Nat.le_add_left ..).trans
    (firstToVote.trans (reelAbove.le.trans (reelToEnd.trans (replayed.trans begun))))
  exact AddressPlan.census_word_of_readout V cfg I_ R_ start K W q piece codes rawWords count₀
    payloadBits L w prefixRoom readout live bus

local notation "room_" => WideFlightCoordinates (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (payloadBits:=payloadBits) (fit:=fit) («begin_»:=censusBase) (rom:=rom)
      («peer»:=peerBank) («old»:=wingBank) («org»:=lookupBase) («homes»:=dateHomes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      («fence»:=upperFence) («count»:=countSlot) («plan»:=freshReel) («j»:=j) («rest»:=rest) («arity»:=arity) («groups»:=groups) («stride»:=stride) («oldTags»:=oldTags) (K:=K)
local notation "primitiveLanes_" => DescentDatedSeedStartup.Primitive.paletteLanes G rot startup.seedWidth Z payloadBits k
local notation "initialSource_" => DescentPackedSeed.Primitive.Source.jobs X S.copies startup.seedWidth payloadBits
local notation "seedEnd_" => (DescentDatedSeedStartup.Input.nodeChart startup k bootHosts (S.groupCount 0)).seedEnd
  (DescentDatedSeedStartup.endAddress X startup bootHosts (S.groupCount 0) k)
local notation "initialBound_" => DescentDatedSeedStartup.Primitive.initialEnd X S.copies startup.seedWidth payloadBits k
  bootHosts (S.groupCount 0) primitiveLanes_ seedEnd_

local notation "sitePagesAt" x₀:arg z₀:arg c₀:arg => WideEarnedSitePages (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (pool:=pool) (raw:=raw) (payloadBits:=payloadBits) (fit:=fit) (rom:=rom)
      (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      («fence»:=fence) («count»:=count) («plan»:=plan) («codec»:=codec) (short:=short) (all:=z₀) (c:=c₀)
      (original:=view x₀) (board:=board) (dateAge:=dateAge) (dateDegree:=dateDegree)
      (datePayload:=datePayload) (ordinaryAt:=ordinaryAt) (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes)
      (previousDate:=previousDate) (priorAddress:=priorAddress) (rosterBank:=rosterBank)
      (datedFloor:=datedFloor) (replayBase:=replayBase) (matrixTable:=matrixAt) (dateTag:=dateTag)
      (dateRotation:=dateRotation) (snapshots:=snapshots) (roleBase:=roleBase) (replayRoom:=replayRoom)
      (datedMem:=capturedAt x₀ z₀)
local notation "matrixAtSource" x₀:arg z₀:arg c₀:arg => primitiveBank x₀ z₀ matrixFloor =
  ((DescentExterior.matrixCode (Branch.pinSpine X G S (issued X G S ordinary reset branch positive room shorten c₀)
    positive base).matrix).val:Computability.VPVNP.BurstRAM.Word w)
local notation "paidPacketsAt" x₀:arg z₀:arg c₀:arg => WideMeasuredPackets (X:=X) (G:=G) (S:=S) (ordinary:=ordinary)
  (reset:=reset) (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (c:=c₀)
  (base:=base) (width:=width) (headerRows:=headerRows) (paidRows:=paidRows)
  («begin_»:=censusBase) («peer»:=peerBank) («old»:=wingBank) («org»:=lookupBase) («homes»:=dateHomes)
  (primitive:=primitiveBank x₀ z₀) (m:=booksBank x₀ z₀)
local notation "registeredAt" x₀:arg z₀:arg c₀:arg din:arg => WideRegisteredDateRows
    (q:=q) (j:=j) (rest:=rest) (W:=W) (piece:=piece) (X:=X) (G:=G) (S:=S) (ordinary:=ordinary)
    (reset:=reset) (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (c:=c₀)
    (board:=board) (dateAge:=dateAge) (dateDegree:=dateDegree) (datePayload:=datePayload)
    (ordinaryAt:=ordinaryAt) (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes)
    (previousDate:=previousDate) (priorAddress:=priorAddress) (rosterBank:=rosterBank)
    (datedFloor:=datedFloor) (replayBase:=replayBase) (matrixTable:=matrixAt) (dateRotation:=dateRotation)
    (snapshots:=snapshots) (roleBase:=roleBase) (dateInput:=din) (datedMem:=capturedAt x₀ z₀)
    (headerRows:=headerRows) (paidRows:=paidRows)


local notation "paidSourceAt" x₀:arg z₀:arg c₀:arg => WideObservedSources (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (pool:=pool) (raw:=raw) (payloadBits:=payloadBits) (fit:=fit) («begin_»:=begin_) (rom:=rom)
      («peer»:=peer) («old»:=old) («org»:=org) («homes»:=homes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      («fence»:=fence) («count»:=count) («plan»:=plan) («codec»:=codec) (short:=short) (all:=z₀) (c:=c₀)
      (primitive:=(primitiveBank x₀ z₀)) (m:=(booksBank x₀ z₀)) (original:=view x₀)
local notation "paidNativeAt" x₀:arg z₀:arg => WideHeldFlightSources (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (payloadBits:=payloadBits) (fit:=fit) («begin_»:=begin_) (rom:=rom)
      («peer»:=peer) («old»:=old) («org»:=org) («homes»:=homes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      («fence»:=fence) («count»:=count) («plan»:=plan) (all:=z₀) (m:=(booksBank x₀ z₀)) (original:=view x₀) («middle»:=middle)
      («cost»:=cost) («arity»:=arity) («groups»:=groups) («stride»:=stride) («oldTags»:=oldTags) (K:=K)


open Lean Elab Term in
local elab "earnedPaidArguments% " fn:term:arg "[" args:term,* "]" : term => do
  let head ← elabTerm fn none
  return mkAppN head (← args.getElems.mapM fun term => elabTerm term none)

set_option maxHeartbeats 7500000 in
include machine in
/-- The same scheduled reset code and addresses serve every choice of the input bits.
The initial checked tape, the retained dated image and its two printed snapshots
are obtained by actual native memory transformations on that assignment. -/
theorem wide_earned_stage_host (bins:W=NativeBranch.binLimit (k:=k) S)
    (packed:packWidth=DescentPackedEpochShelves.grain (payloadBits/2) G.C)
    (seedWord:2*digitsNeeded s≤payloadBits) (epochWord:2*DescentPackedEpochShelves.unit G.C≤payloadBits/2)
    (edgeWord:2^j*s≤w) (seatsWord:S.batch+2*packWidth<2^w)
    (reelAbove:dst<DescentExteriorMatrixUpdate.Calendar.earlyAt S k tail replayBase)
    (headerBelow:head<censusBase) (headerVote:head<front+extra ∨ dst<head)
    (shopCount:(dateSpec).scalar.shops=(dateHardware).hosts)
    (alive:0<(dateSpec).scalar.shops)
    (priorMetadata:(dateOut).metadataEnd dateOrigin≤earlyFloor) (one:chunks (dateHardware).groups (dateHardware).lanes=1)
    (roleEnd:roleBase+DescentTerminalRoleTables.count roleBankBits≤(dateSpec).cohortEnd censusBase)
    (layout:(dateSpec).Before censusBase paidBank actorBank wingBank peerBank (lookupPage).total (lookupPage).modulo
      dateHomes (lookupPage).boundaries)
    (paidRowsFit:∀b₀,(dateSpec).scalar.shops≤(paidBank b₀).size)
    (signedRows:∀b₀ j₀,(dateSpec).scalar.shops≤(wingBank b₀ j₀).size)
    (rankDirectory:ℕ→Bank) (rankShape:snapshots=Chronology.SnapshotCalendar reset
      (Chronology.kindCalendar S.rounds S.height) (capCalendar G.b S.rounds g S.height) rankDirectory)
    (rankFloor:ℕ) (rankFloorBound:rankFloor≤replayBase) (rankRole:rankFloor≤roleBase)
    (rankAway:∀i<S.length,∀ rankedBank : Bank, snapshots.compact i = some rankedBank →
      rankedBank.base+rankedBank.size≤capture ∨ capture+(captureDates).length ≤ rankedBank.base)
    (retainedWidth:j≤S.groupWidth k tail S.length+k)
    (replayPayload:(k*S.length+1)*2^(8+S.capGain*S.length)≤w)
    (signedFit:DescentSignedCableCodec.width 3 256*startup.packedLanes≤w)
    (fieldsFit:startup.operandBits*startup.operandLanes≤w) (headerLow:startingHeader<startup.base)
    (sourceSpace:DescentPackedSeed.publicWords X+DescentDyadicSpan.span initialSource_≤ seedEnd_)
    (liveness:0<primitiveLanes_) (embed:payloadBits≤w) (bootRoom:initialBound_<2^w)
    (sameHeader:head=startingHeader) (floors:ℕ→ℕ)
    (recorded:∀(x₀:extPins→Bool)(z₀:Full→Bool),
      lo+extent packWidth steps≤ startingHeader → startingHeader< initialBound_ →
      (∀a∈shelves packWidth lo 0 steps,∀i:Fin (DescentPackedProfileTape.slots a.src.seats packWidth),
        (startedAt x₀ z₀) (a.base+i.val)=((DescentPackedProfileTape.packed a.src.pin (histAt z₀) packWidth i.val).val:Computability.VPVNP.BurstRAM.Word w)) →
      (DatePorts.initial G rot X S.copies startup k bootHosts (S.groupCount 0) payloadBits Z).held
        (honestAt z₀).origin.source initialBound_ (startedAt x₀ z₀) →
      (startedAt x₀ z₀) startingHeader=0 →
      Chronology.FundedDateInputs S datesAt (startedAt x₀ z₀)
      startingHeader capture replayBase floors countAt dateRotation ((honestAt z₀).path.dateReadbacks
        (DateCode.history datesAt (startedAt x₀ z₀)) dateTag dateRotation countAt
        ((chart).rows (histAt z₀)).length (acceptAt z₀)) ∧
        ((acceptAt z₀)→(honestAt z₀).path.Held startingHeader (lastAt x₀ z₀)) ∧
        ∀c₀:(last).Choice,(chart).read (histAt z₀)=some c₀→
          (issued X G S ordinary reset branch positive room shorten c₀).path.snapshotRanks
            snapshots rankFloor (lastAt x₀ z₀))
    (batchFit:S.batch<2^w) (captureAt:capture=seedBase+seedRows+1)
    (countShelf:lo=DescentWideSeedFlags.selectorBase X S.copies s payloadBits (steps).length) (archiveEnd:front+extra≤ startingHeader) (reelData:front+extra≤replayBase)
    (below:compact+32*DescentExteriorShelf.span j rest s datePorts≤replayBase)
    (headLow:head<replayBase) (headApart:head<capture ∨ capture+(captureDates).length≤head)
    (preRole:compact+32*DescentExteriorShelf.span j rest s datePorts≤roleBase)
    (rotRole:∀i<S.length,dateRotation i<roleBase)
    (startupRole:startingHeader<roleBase) (headRole:head<roleBase)
    (earned:∀(x₀:extPins→Bool)(z₀:Full→Bool)(c₀:(last).Choice),candidatePrior x₀ (erased z₀)=some c₀→
      ∀din:(dateMachine).DateInputs ((dateMachine).stageStart datedFloor) w,
      registeredAt x₀ z₀ c₀ din→paidPacketsAt x₀ z₀ c₀→matrixAtSource x₀ z₀ c₀→sitePagesAt x₀ z₀ c₀)
    (returned:∀(x₀:extPins→Bool)(z₀:Full→Bool)(c₀:(last).Choice),candidatePrior x₀ (erased z₀)=some c₀→
      ∃din:(dateMachine).DateInputs ((dateMachine).stageStart datedFloor) w,registeredAt x₀ z₀ c₀ din)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (headerRoom:(cfg).terminal.pool≤headerRows) (headersPositive:0<headerRows)
    (chipRows:(cfg).terminal.rows=K*W) (dataRoom:q*p≤w)
    (word:Nat.log 2 (NativeBranch.privateMax G S p)+1≤w)
    (slotCapacity:numSlots≤DescentDyadicSpan.span (cfg).terminal.rows)
    (hp:pcs≤2^(w+1)) (hr:regs≤2^(w+1))
    (ht:runtime+obs≤2^(CheapISA.width w+1))
    (budget rate:ℕ) (height:4≤budget) (widthRate:w≤rate*budget)
    (addr:(CheapISA.dataBase pcs regs+firstFree)+(runtime+obs)≤2^(3*budget))
    (Y:Approximation F cp (Tagged.pins budget budget))
    (M₀ J₀ price:ℕ)
    (bill_:(4*((seedNet).cells+(seedNet).internal)+9*(rawWords*widthWord)+binsPaid*countWidth_+
      Fintype.card Full+Fintype.card extPins+
      (257*(1000*(2*(7*(rate+6))+2)*(2*4^7+1))+256*fixedISAPrice*(rate+6))*
        (pcs+regs+firstFree+fuel+obs+2^budget+1)*(budget+1))*2^J₀≤price*(S.copies*s)*(M₀+2^J₀*E₀)) :
    ∃calls:ℕ,∃H:Host F cp ((S.copies*s)*P) (Sockets (List.replicate calls (CollapseOracle.tagCall budget Y))),
      Agrees (independentCopies (S.copies*s) X) (tableApprox H.width (exactValue _ H)) ∧
      hostSize H*2^J₀≤price*(S.copies*s)*(M₀+2^J₀*E₀) := by
  have seedBefore : seedBase+(seedRows+1)≤lo := by
    rw [countShelf]
    unfold DescentWideSeedFlags.selectorBase
    omega
  have dated (x₀ : extPins→Bool) (z₀ : Full→Bool) := by
    obtain ⟨beforeHeader,belowHeader,shelvesAt⟩ :=
      complete_appended_profile_after G rot X (S.initialDigits ordinary.radix) hostsEnough startup
        startingHeader payloadBits Z s (chart).seed lo G.C packWidth steps compact extra
        (DescentExterior.publicRows X (view x₀))
        (Sum.elim (histAt z₀) (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inr))
        (DescentTerminalPublicIdentity.back (z₀ ∘ DescentTerminalFullPins.chip) w codes count₀)
        seedWord sourceSpace liveness embed signedFit fieldsFit seedBefore le_rfl archiveEnd headerLow bootRoom
    exact recorded x₀ z₀ beforeHeader belowHeader shelvesAt
      (initial_held_of_public G rot X (S.initialDigits ordinary.radix) hostsEnough startup
        startingHeader payloadBits Z (honestAt z₀).origin (checkedAt x₀ z₀)
        signedFit fieldsFit headerLow sourceSpace liveness embed bootRoom)
      (complete_after_count G rot X (S.initialDigits ordinary.radix) hostsEnough startup
        startingHeader payloadBits Z (honestAt z₀).origin ((honestAt z₀).origin.seed.hostSize.le.trans hostsEnough)
        (checkedAt x₀ z₀) signedFit fieldsFit headerLow sourceSpace liveness embed bootRoom).2.1
  have datedHeld (x₀:extPins→Bool) (z₀:Full→Bool) (alive:∃v,whichAt x₀ z₀=some v) :
      (honestAt z₀).path.Held head (lastAt x₀ z₀) := by
    obtain ⟨v,selected⟩:=alive
    rw [sameHeader]
    exact (dated x₀ z₀).2.1 ⟨v,((DescentExteriorShelf.proposed_eq _ _ _ _ v).mp selected).1⟩
  have archivedRanks (x₀:extPins→Bool) (z₀:Full→Bool) (c₀:(last).Choice) (read:whichAt x₀ z₀=some c₀) :
      (issued X G S ordinary reset branch positive room shorten c₀).path.snapshotRanks snapshots rankFloor (lastAt x₀ z₀) :=
    (dated x₀ z₀).2.2 c₀ ((DescentExteriorShelf.proposed_eq _ _ _ _ c₀).mp read).1
  have capturedRotations (x₀:extPins→Bool) (z₀:Full→Bool) (c₀:(last).Choice)
      (selected:whichAt x₀ z₀=some c₀) :
      (issued X G S ordinary reset branch positive room shorten c₀).path.RotationWords
        dateTag dateRotation (capturedAt x₀ z₀) := by
    have read:(chart).read (histAt z₀)=some c₀:=((DescentExteriorShelf.proposed_eq _ _ _ _ c₀).mp selected).1
    have stored:histAt z₀=(chart).store c₀:=((chart).read_iff _ _).mp read
    have chosen:c₀=selectedAt z₀:=
      ((congrArg (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow stored).trans ((normalizedRoute X G S ordinary reset branch positive room shorten w fit).stored c₀)).symm
    rw [chosen]
    have live:=(dated x₀ z₀).1
    have words:=(honestAt z₀).path.retained_words (DateCode.history datesAt (startedAt x₀ z₀))
      dateTag dateRotation countAt ((chart).rows (histAt z₀)).length (acceptAt z₀)
      live.observed floors startingHeader live.countApart live.matrixApart live.countBefore
      live.matrixBefore live.frame ordinary.radix le_rfl batchFit
    apply Path.RotationWords.move (honestAt z₀).path dateTag dateRotation (words.2 ⟨c₀,read⟩)
    intro i hi
    exact (roleMount.frame _ _ (.inl (rotRole i hi))).trans
      (DescentLowCountBook.frame capture rowAddress (lastAt x₀ z₀) (captureDates).length (dateRotation i)
        (.inr (live.rotationsLow i hi)))
  let sample : (last).Choice := selectedAt (fun _ : Full=>false)
  let words : Full→Bool :=
    Sum.elim (Sum.elim (Sum.elim ((chart).store sample) (fun _=>false)) (fun _=>false)) (fun _=>false)
  have readSample : (chart).read (histAt words)=some sample := ((chart).read_iff _ _).mpr rfl
  have physicalSample := (dated (fun _=>false) words).2.2 sample readSample
  have rank (i:ℕ) (hi:i<S.length) (storedBank:Bank) (stored:snapshots.compact i=some storedBank) :
      storedBank.Fits w ((dateCalendar).scratch sliceEnd) := by
    have bankRoom := (issued X G S ordinary reset branch positive room shorten sample).path.snapshot_rank_rooms
      snapshots rankFloor _ physicalSample i hi storedBank stored
    have first : replayBase≤DescentExteriorMatrixUpdate.Calendar.earlyAt S k tail replayBase := by
      unfold DescentExteriorMatrixUpdate.Calendar.earlyAt DescentExteriorMatrixUpdate.Calendar.stop
        DescentExteriorMatrixUpdate.Calendar.tableAt
      omega
    have datedFloorLe : DescentExteriorMatrixUpdate.Calendar.earlyAt S k tail replayBase≤earlyFloor :=
      Nat.le_add_right ..
    have slices : earlyFloor ≤ sliceEnd := by
      change earlyFloor ≤ earlyFloor + _ + _ + _
      exact ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
    exact ⟨bankRoom.1,bankRoom.2.1,bankRoom.2.2.trans (rankFloorBound.trans
      (first.trans (datedFloorLe.trans (slices.trans ((dateCalendar).addresses sliceEnd 0).1))))⟩
  have tags := (dated (fun _=>false) (fun _=>false)).1
  have rotHi := tags.rotationsHigh
  have cutAfter : readoutEnd_≤cut_:=Nat.le_add_right ..
  have stopAfter : cut_ ≤ stop_ := by
    change cut_ ≤ cut_ + _ + _ + _ + _ + _
    exact Nat.le_add_right_of_le (Nat.le_add_right_of_le (Nat.le_add_right_of_le
      (Nat.le_add_right_of_le (Nat.le_add_right _ _))))
  have lastFit : readoutEnd_ < 2^w :=
    (cutAfter.trans stopAfter).trans_lt ((Nat.lt_succ_self _).trans censusRoom)
  have wordPositive : 0 < w := (Nat.zero_lt_succ _).trans_le word
  have traceWord : DescentTerminalThreshold.depth widthWord≤w+1 := Nat.add_le_add_right ((Nat.log2_le_self _).trans dataRoom) 1
  have ⟨geometry,earlyRoom,later,matrixRoom⟩:=scheduled_flight_geometry
    («template»:=template) («sitesPositive»:=sitesPositive) («rawWords»:=rawWords) («headerRows»:=headerRows) («paidRows»:=paidRows)
    («payloadBits»:=payloadBits) («rom»:=rom) («other»:=other) («lo»:=lo) («packWidth»:=packWidth)
    («head»:=head) («board»:=board) («dateAge»:=dateAge) («dateDegree»:=dateDegree) («datePayload»:=datePayload)
    («ordinaryAt»:=ordinaryAt) («operandLanes»:=operandLanes) («primitiveLanes»:=primitiveLanes) («previousDate»:=previousDate) («priorAddress»:=priorAddress)
    («rosterBank»:=rosterBank) («datedFloor»:=datedFloor) («replayBase»:=replayBase) («dateTag»:=dateTag) («dateRotation»:=dateRotation)
    («snapshots»:=snapshots) («capture»:=capture) («W»:=W) («q»:=q) («piece»:=piece)
    («K»:=K) («j»:=j) («rest»:=rest) («arity»:=arity) («groups»:=groups)
    («stride»:=stride) («oldTags»:=oldTags)
    (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive)
    (room:=room) (shorten:=shorten) (fit:=fit)
    (bins:=bins) (packed:=packed) (shelf:=countShelf) (position:=captureAt)
    (seedWord:=seedWord) (epochWord:=epochWord) (architecture:=embed) (chipWord:=dataRoom)
    (edgeWord:=edgeWord) (seatsWord:=seatsWord) (rotations:=rotHi)
    (reelAbove:=reelAbove) (headerBelow:=headerBelow) (headerVote:=headerVote) (placed:=layout)
    (dictionary:=romTop) (lastFit:=lastFit)
  have fenceFits : upperFence < 2^w :=
    ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans_lt matrixRoom
  have addressRoom : (dateSpec).maskBase censusBase < 2^w := by
    subst W
    exact fenceFits
  have lastAbove : wall≤readoutEnd_ := by
    obtain ⟨_,_,flight_,issued_,ended_⟩:=AddressPlan.stages cfg I_ base_
    exact flight_.trans (issued_.trans ended_)
  have bounds_ := geometry
  obtain ⟨_,_,_,_,_,_,_,archive_,vote_,_⟩:=bounds_
  have voteBefore : dst<readoutEnd_:=vote_.trans_le lastAbove
  have initialRoom : firstFree ≤ 2^w := archive_.trans fenceFits.le
  have actualBoot : front+DescentTerminalChipBootWords.total K W q piece codes≤firstFree:=by
    apply Nat.add_le_add_left
    exact ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  have beforeArena : start≤base_:=by
    have counter : start≤(meter V R_ start).base:=Nat.le_add_right ..
    refine counter.trans ?_
    change (meter V R_ start).base ≤ (meter V R_ start).base + _ + _ + _ + _
    exact Nat.le_add_right_of_le (Nat.le_add_right_of_le (Nat.le_add_right_of_le (Nat.le_add_right _ _)))
  have chipRoom : DescentTerminalChipRuntime.Room cpu bankSet w (K*W) numSlots :=by
    have fitted := AddressPlan.chip_room (K:=K) (W:=W) (q:=q) («p»:=piece)
      (S:=cfg) (I:=I_) (base:=base_) (O:=O_) («codes»:=codes) («front»:=front) (empty:=emptyCode)
      (actualBoot.trans (archive_.trans beforeArena)) chipRows lastFit
    simpa only [chipRows] using fitted
  have before (i : Unit) : (cols).seed i<cut_ :=
    (AddressPlan.readout_seed_below V cfg I_ R_ start head dst i).trans_le cutAfter
  have occupiedKey : 0<numBins:=
    (DescentTerminalChronologicalBooks.empty q tagCount cap nodeCap cap p venues p).pos
  have widthFit : widthWord<2^w:=dataRoom.trans_lt Nat.lt_two_pow_self
  have ready : Ready tapeDesc banks_ cut_ stop_ rawWords widthWord :=
    DescentTerminalLast.trailing_ready tapeDesc
      (AddressPlan.readout_inputs V cfg I_ R_ start head dst (K*W) chipRoom.count voteBefore headersPositive)
      (AddressPlan.readout_key_cap V cfg I_ R_ start head dst (K*W) slotCapacity) widthFit occupiedKey censusRoom
  have countBudget : NativeBranch.privateMax G S p+numSlots<2^countWidth_:=by
    have slotBound : numSlots≤readoutEnd_:=Nat.le_add_left ..
    have deadBound : NativeBranch.privateMax G S p<2^w:=
      (Nat.lt_pow_succ_log_self (by decide : 1<2) _).trans_le (Nat.pow_le_pow_right (by decide : 0<2) word)
    simpa only [pow_succ, Nat.mul_two] using (Nat.add_lt_add deadBound (slotBound.trans_lt lastFit))
  have paidCap (t : (last).Choice) : charge t≤NativeBranch.privateMax G S p :=
    (leaf_unitExponent X G S ordinary reset branch positive room shorten t base width age wFit qFit qh cfg pool raw ()).symm.le.trans
      (Branch.unitExponent_le X G S (issued X G S ordinary reset branch positive room shorten t) positive
        (Nat.le_max_left 1 (max reset.bitsR (C*reset.bitsR))))
  have seedFit (t : (last).Choice) : charge t<2^w :=
    (paidCap t).trans_lt ((Nat.lt_pow_succ_log_self (by decide : 1<2) _).trans_le
      (Nat.pow_le_pow_right (by decide : 0<2) word))
  have countsFit (t : (last).Choice) :
      Fintype.card (DescentTerminalSeedFactors.Occurs (fun _:Unit=>charge t) (Fin numSlots))<2^countWidth_ := by
    simpa [DescentTerminalSeedFactors.Occurs] using (Nat.add_le_add_right (paidCap t) numSlots).trans_lt countBudget
  have ⟨seedLeft,captureSize,historyLow⟩:=scheduled_capture_coordinates
    («payloadBits»:=payloadBits) («lo»:=lo) («capture»:=capture) («W»:=W) («piece»:=piece)
    (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive)
    (room:=room) (shorten:=shorten) (fit:=fit) (packWidth:=packWidth) (location:=captureAt) (shelf:=countShelf)
  have physicalDates (x₀:extPins→Bool) (z₀:Full→Bool) :=
    let live:=(dated x₀ z₀).1
    mounted_scheduled_wide_from_dates
      («X»:=X) («G»:=G) («S»:=S) («ordinary»:=ordinary) («reset»:=reset)
      («branch»:=branch) («positive»:=positive) («room»:=room) («shorten»:=shorten) («base»:=base)
      («width»:=width) («template»:=template) («sitesPositive»:=sitesPositive) («rawWords»:=rawWords) («headerRows»:=headerRows)
      («paidRows»:=paidRows) («payloadBits»:=payloadBits) («fit»:=fit) («rom»:=rom) («other»:=other)
      («lo»:=lo) («packWidth»:=packWidth) («head»:=head) («j»:=j) («rest»:=rest)
      («arity»:=arity) («groups»:=groups) («stride»:=stride) («oldTags»:=oldTags) («K»:=K)
      («W»:=W) («q»:=q) («piece»:=piece)
    (original:=view x₀) (all:=z₀)
      (datedMem:=capturedAt x₀ z₀) (matrixTable:=matrixAt)
      (board:=board) (dateAge:=dateAge) (dateDegree:=dateDegree) (datePayload:=datePayload)
      (ordinaryAt:=ordinaryAt) (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes)
      (previousDate:=previousDate) (priorAddress:=priorAddress) (rosterBank:=rosterBank)
      (datedFloor:=datedFloor) (replayBase:=replayBase) (dateTag:=dateTag) (dateRotation:=dateRotation)
      (snapshots:=snapshots) (roleBase:=roleBase) (replayRoom:=replayRoom)
      (hostsEnough:=hostsEnough) (startup:=startup) (startingHeader:=startingHeader)
      (datesAt:=datesAt) (capture:=capture) (countAt:=countAt)
      bins geometry shopCount addressRoom wordPositive alive priorMetadata one rank roleEnd layout paidRowsFit
      signedRows ((honestAt z₀).origin.seed.hostSize.le.trans hostsEnough) signedFit fieldsFit headerLow sourceSpace liveness embed bootRoom live.run live.cheap floors
      live.order live.observed live.countApart live.matrixApart live.countBefore live.matrixBefore live.frame batchFit seedLeft captureSize.le
      historyLow archiveEnd reelData below live.counts live.rotationsLow live.rotationsHigh earlyRoom later matrixRoom headLow headApart
      (datedHeld x₀ z₀) rfl roleMount preRole rotRole startupRole headRole rfl
  have paidNative (x₀ : extPins → Bool) (z₀ : Full → Bool) : paidNativeAt x₀ z₀ :=
    (physicalDates x₀ z₀).1
  have paidSource (x₀ : extPins → Bool) (z₀ : Full → Bool) (c₀ : (last).Choice)
      (selected : candidatePrior x₀ (erased z₀) = some c₀) : paidSourceAt x₀ z₀ c₀ := by
    obtain ⟨din, dated⟩ := returned x₀ z₀ c₀ selected
    exact @earned_packet_publication_from_reset
      F _ cp P X G S
      k cut tail n h C f
      g W q piece ordinary reset branch
      positive room shorten c₀ j rest base
      width age wFit qFit qh template sitesPositive
      rawWords headerRows paidRows pool raw w K
      payloadBits fit rom other arity groups stride
      oldTags codec lo packWidth z₀ head short
      fence count plan (view x₀) boardDegree board dateAge
      dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress
      rosterBank datedFloor replayBase matrixAt dateTag dateRotation snapshots
      roleBase (capturedAt x₀ z₀) din replayRoom bins shopCount alive
      priorMetadata one roleEnd layout paidRowsFit signedRows rankDirectory
      rankShape (lastAt x₀ z₀) rankFloor capture (captureDates).length rowAddress roleMount
      rfl (archivedRanks x₀ z₀ c₀ selected) rankFloorBound rankRole rankAway (capturedRotations x₀ z₀ c₀ selected) addressRoom
      wordPositive rotHi below retainedWidth replayPayload dated ((physicalDates x₀ z₀).2 c₀ selected)
      (earned x₀ z₀ c₀ selected din dated)
  exact earnedPaidArguments% (@wide_paid_stage_host) [
    F, (inferInstance : Field F), cp, P, X, G, S, k, cut, tail, n, h, C, f, g, W, q, piece,
    ordinary, reset, branch, positive, room, shorten, j, rest, base, width, age, wFit, qFit, qh,
    template, sitesPositive, rawWords, headerRows, paidRows, pool, raw, w, K, payloadBits, fit,
    begin_, rom, peer, old, org, homes, other, lo, packWidth, head, short, fence, count, plan,
    middle, cost, primitiveBank, booksBank, machine, countWidth_, cut_, stop_, banks_, paidNative,
    paidSource, romTop, headerRoom, headersPositive, chipRoom, dataRoom, word, wordPositive, ready,
    hp, hr, initialRoom, ht, before, traceWord, (show countWidth_ ≤ w+1 from le_rfl),
    (Nat.zero_lt_succ w), seedFit, countsFit, budget, rate, height, widthRate, addr, Y, M₀, J₀,
    price, bill_]


end
end Hierarchy.DescentSixParty.SeedNamed



-- Skip the costly local suggestion index for these large theorem types during export.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun prior =>
  ["wide_earned_native_bill", "wide_earned_stage_host"] ++ prior

end OAI

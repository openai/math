import OAI.Hierarchy.DescentNamedSelectorCapture
import OAI.Hierarchy.DescentNamedWidePrimitiveSources
import OAI.Hierarchy.DescentNamedOriginalFundedMiddle
import OAI.Hierarchy.DescentMountedOriginalFundedMiddle

namespace OAI
/-! # The original dated program at the native terminal preflight and book addresses -/
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
variable (original:Port ((2^(j+(j+rest))*(S.firstWidth G.b (W*piece)))*P) (CorrectionFrame.copiesWidth (2^(j+(j+rest))*(S.firstWidth G.b (W*piece))) X.width)→Bool)

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
variable (dateInput : ((PhysicalReset.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset) (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).DateInputs (((PhysicalReset.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset) (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).stageStart datedFloor) w)
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
variable (replayRoom : ((replayCalendar X S k tail j rest snapshots)).stop (((((preflightSpec X G S k g (W*piece) tail (geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows))).scanPages (((replayCalendar X S k tail j rest snapshots)).packetEnd (((Phase.scheduled G S board k tail dateAge (W*piece) f g (max 1 (max reset.bitsR (C*reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset) operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor)).stop (DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail replayBase j rest (S.firstWidth G.b (W*piece)) (Fintype.card (Port P X.width))))) q)).stop)<2^w)
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
local notation "bookControl" x:arg => portTable (G:=4) («V»:=(x).vertices) (M:=(x).vertices*(x).arguments)
  (A:=(x).arguments) (a:=Book.tokenBits ((x).vertices*(x).arguments)) q
local notation "postBook" x:arg => (x).afterSiteControls censusBase q p peerBank wingBank
  (((x).scanPages lookupBase q).total) (((x).scanPages lookupBase q).modulo) dateHomes
  (((x).scanPages lookupBase q).boundaries)
  (((x).controls censusBase).after (bookControl x) (Book.expression ((x).parts censusBase)) bookImage_)

local notation "count₀" => E₀*2^(j+rest)
local notation "codes" => DescentTerminalScalarHeader.range q tagCount cap nodeCap cap p venues
local notation "seed" => (chart).seed
local notation "front" => end_ (lo+extent packWidth steps) G.C packWidth+17*DescentExteriorShelf.span j rest s E₀
local notation "extra" => DescentTerminalPublicIdentity.total K W q piece codes rawWords count₀
local notation "paint" => all ∘ DescentTerminalFullPins.chip
local notation "history_" => all ∘ DescentTerminalFullPins.history ∘ Sum.inl
local notation "past_" => all ∘ DescentTerminalFullPins.history ∘ Sum.inr
local notation "seedBase" => DescentWideSeedFlags.endInput X S.copies s payloadBits
local notation "seedRows" => DescentPackedSeed.rows X S.copies s payloadBits
local notation "tape" => Root.widePackedImage X S.copies s payloadBits w seed lo G.C packWidth steps compact
  (DescentExterior.publicRows X original) (Sum.elim history_ past_)
local notation "backing" => DescentTerminalPublicIdentity.back paint w codes count₀
local notation "originalTape" => Root.appended front extra tape backing
local notation "checked" => DescentWideSeedFlags.countedAt X S.copies s payloadBits seed history_ originalTape
open Chronology DescentDatedSeedStartup.Input DescentTerminalEpochDecoder DescentPackedSeed DescentExteriorShelf
variable {bootHosts:ℕ} (hostsEnough:Fintype.card (Vertex X)≤bootHosts) (startup:DescentDatedSeedStartup.Layout)
  (startingHeader:ℕ) (datesAt:ℕ→DateCode w) (capture:ℕ) (countAt:ℕ→ℕ)
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
   (Branch.historyCountReel X S replayBase dateTag dateRotation countAt capture matrixTable k tail j rest s w)).seq termCode
local notation "originalCost" => (DateCode.afterTicks bootCost datesAt S.length+
    ((4+11*(captureDates).length)+DescentExteriorMatrixUpdate.Calendar.earlyClock S k tail j rest s datePorts))+termCost
local notation "upperFence" => (pre).maskBase censusBase
local notation "freshReel" => (oldReel).late upperFence
local notation "countSlot" => fun i:ℕ=>capture+i
local notation "chosen_" => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow history_
local notation "honest" => issued X G S ordinary reset branch positive room shorten chosen_
local notation "accepted" => ∃c,(chart).read history_=some c
local notation "layout_" => fun c=>Branch.publicLayout X G S (issued X G S ordinary reset branch positive room shorten c)
  positive base width
local notation "which_" => proposed (chart).read layout_ (DescentExterior.publicRows X original)
  (all ∘ DescentTerminalFullPins.history)
local notation "flightFor_" program_:arg clocks_:arg => WideHeldFlightSources (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (payloadBits:=payloadBits) (fit:=fit) (begin_:=censusBase) (rom:=rom)
      (peer:=peerBank) (old:=wingBank) (org:=lookupBase) (homes:=dateHomes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=upperFence) (count:=countSlot) (plan:=freshReel) (all:=all) (m:=bookImage_) (original:=original) (middle:=program_)
      (cost:=clocks_) (arity:=arity) (groups:=groups) (stride:=stride) (oldTags:=oldTags) (K:=K)
local notation "flight_" => flightFor_ originalMid originalCost
local notation "room_" => WideFlightCoordinates (j:=j) (rest:=rest) (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (payloadBits:=payloadBits) (fit:=fit) (begin_:=censusBase) (rom:=rom)
      (peer:=peerBank) (old:=wingBank) (org:=lookupBase) (homes:=dateHomes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=upperFence) (count:=countSlot) (plan:=freshReel) (arity:=arity) (groups:=groups) (stride:=stride) (oldTags:=oldTags) (K:=K)
/-- The code stores the seed verdict first, then one count per ordinary date, then
the packed shelf. The copy ends at the first shelf word. -/
theorem scheduled_capture_coordinates
    (location : capture=seedBase+seedRows+1)
    (shelf : lo=DescentWideSeedFlags.selectorBase X S.copies s payloadBits (steps).length) :
    seedBase+seedRows<capture ∧ capture+(captureDates).length=lo ∧ lo≤compact := by
  have sized : (captureDates).length=(steps).length :=
    scheduled_capture_length (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset)
      (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (fit:=fit)
  refine ⟨by omega, ?_, ?_⟩
  · rw [location,sized,shelf]
    rfl
  · change lo≤lo+_+_+_
    omega

local notation "routeTables_" => (RouteSources.Tables.mk 4 venues (venues*NativeBranch.localLimit G S)
  (NativeBranch.localLimit G S) (Book.tokenBits (venues*NativeBranch.localLimit G S)) W q K)
local notation "reachedInput_" => (pre).reachedInput censusBase rom q piece W K codes front peerBank wingBank
  ((pre).scanPages lookupBase q).total ((pre).scanPages lookupBase q).modulo dateHomes
  ((pre).scanPages lookupBase q).boundaries cfg V other routeTables_ (pre).vertices B
local notation "finalEnd_" => AddressPlan.last V cfg reachedInput_ ((pre).channels censusBase) upperFence
local notation "votedAt_" => finalAt (front+extra) lo packWidth steps

/-- One additional counter bit holds all occurrences of the native exponent and
all physical terminal slots. Both summands already fit the original word. -/
theorem scheduled_counter_budget
    (seedBound : Nat.log 2 (NativeBranch.privateMax G S p)+1≤w)
    (endBound : finalEnd_<2^w) :
    NativeBranch.privateMax G S p+(cfg).terminal.pool<2^(w+1) := by
  have slotBound : (cfg).terminal.pool≤finalEnd_:=Nat.le_add_left ..
  have privateBound : NativeBranch.privateMax G S p<2^w :=
    (Nat.lt_pow_succ_log_self (by decide : 1<2) _).trans_le
      (Nat.pow_le_pow_right (by decide : 0<2) seedBound)
  rw [pow_succ]
  omega

/-- The two rotation traversals and the terminal word bounds are obtained from
the physical calendar, the original count copy, and the end of the placed program. -/
theorem scheduled_flight_geometry
    (bins : W=NativeBranch.binLimit (k:=k) S)
    (packed : packWidth=DescentPackedEpochShelves.grain (payloadBits/2) G.C)
    (shelf : lo=DescentWideSeedFlags.selectorBase X S.copies s payloadBits (steps).length)
    (position : capture=seedBase+seedRows+1)
    (seedWord : 2*digitsNeeded s≤payloadBits) (epochWord : 2*DescentPackedEpochShelves.unit G.C≤payloadBits/2)
    (architecture : payloadBits≤w) (chipWord : q*p≤w) (edgeWord : 2^j*s≤w)
    (seatsWord : S.batch+2*packWidth<2^w)
    (rotations : ∀i<S.length,dateRotation i<replayBase)
    (reelAbove : votedAt_<Calendar.earlyAt S k tail replayBase)
    (headerBelow : head<censusBase) (headerVote : head<front+extra ∨ votedAt_<head)
    (placed : (dateSpec).Before censusBase paidBank actorBank wingBank peerBank
      (lookupPage).total (lookupPage).modulo dateHomes (lookupPage).boundaries)
    (dictionary : rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase censusBase)
    (lastFit : finalEnd_<2^w) :
    room_ ∧ earlyFloor<2^w ∧ matrixEnd≤upperFence ∧ upperFence+S.length+1<2^w := by
  have ageFits : S.length≤H₀ :=
    ordinary_age_room (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (room:=room) S.length
  have livePlacement :
      (pre).Before censusBase paidBank actorBank wingBank peerBank
        ((pre).scanPages lookupBase q).total ((pre).scanPages lookupBase q).modulo dateHomes
        ((pre).scanPages lookupBase q).boundaries := by
    subst W
    exact placed
  have low : earlyFloor ≤ sliceEnd := by
    change earlyFloor ≤ earlyFloor + _ + _ + _
    exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  obtain ⟨e₁,e₂,e₃,_⟩:=(dateCalendar).addresses sliceEnd censusBase
  have replayed : earlyFloor≤censusBase :=
    low.trans (e₁.trans (e₂.trans (e₃.trans (Nat.le_add_right ..))))
  have startLow : censusBase≤upperFence :=by
    obtain ⟨a,b₁,c₁,d,e,f₁,g₁,h₁,i⟩:=(pre).layers censusBase
    have base_ := (pre).cohort_le censusBase
    omega
  have gap := AddressPlan.late_gap V cfg reachedInput_ ((pre).channels censusBase) upperFence S.length ageFits
  obtain ⟨_,_,after_,done_,last_⟩:=AddressPlan.stages cfg reachedInput_
    (afterMeter V cfg ((pre).channels censusBase) upperFence)
  have matrixFit : upperFence+S.length+1<2^w :=
    (gap.trans (after_.trans (done_.trans last_))).trans_lt lastFit
  have earlyBound : earlyFloor<2^w:=by omega
  have hspan : 0<DescentExteriorShelf.span j rest s datePorts:=Nat.two_pow_pos _
  have calendarEnd : matrixEnd+S.length+1+17*DescentExteriorShelf.span j rest s datePorts≤earlyFloor:=
    Nat.add_le_add_left (Nat.le_max_left ..) _
  have reelRoom := DescentExteriorMatrixUpdate.Calendar.room S k tail replayBase dateTag dateRotation
    rotations (by omega : matrixEnd+S.length+2<2^w)
  refine ⟨?_,earlyBound,by omega,matrixFit⟩
  exact wide_flight_coordinates (j:=j) (rest:=rest) (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (payloadBits:=payloadBits) (fit:=fit) (begin_:=censusBase) (rom:=rom)
      (peer:=peerBank) (old:=wingBank) (org:=lookupBase) (homes:=dateHomes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=upperFence) (count:=countSlot) (plan:=freshReel) (arity:=arity) (groups:=groups) (stride:=stride) (oldTags:=oldTags) (K:=K)
    oldReel matrixEnd replayBase paidBank actorBank rfl rfl packed shelf
    (fun i _=>by rw [position]) seedWord epochWord architecture chipWord edgeWord seatsWord
    ageFits reelRoom reelAbove replayed headerBelow headerVote livePlacement dictionary lastFit

local notation "capturedRows_" => ∀c₀,which_=some c₀→
  DescentTerminalFundedReadback.Capture lo compact j rest s E₀ extra checked (postBook pre)
    ((issued X G S ordinary reset branch positive room shorten c₀).path.savedRotations
      freshReel upperFence tail (postBook pre)) ∧ room_

/-- The scheduled CPU, memory and charge of the actual dated program are fixed
simultaneously. Its final packed pages are the ones that the reached terminal code reads. -/
theorem scheduled_wide_native_at (middleCode : Procedure w) (middleCost : ℕ) (bins:W=NativeBranch.binLimit (k:=k) S) (geometry:room_)
    (later:matrixEnd≤upperFence) (space:upperFence+S.length+1<2^w)
    {extraReads:Memory w→Prop}
    (paid:DescentTerminalFundedReadback.Receipt middleCode middleCost checked postEntry_
      (seedBase+seedRows) lo compact j rest s E₀ extra
      (fun out=>(∀i v,i<((chart).rows history_).length→(honest).path.selections[i]?=some v→
        (out (capture+i)).val=selectionCount G v) ∧
        (accepted→(honest).path.savedRotations oldReel matrixEnd tail out) ∧ extraReads out))
    (held:(∃v,which_=some v)→(honest).path.Held head postEntry_) : flightFor_ middleCode middleCost ∧ capturedRows_ := by
  have same:postEntry_=postBook pre:=by subst W;rfl
  let recorded (outputMemory : Memory w) : Prop := DescentTerminalFundedReadback.Receipt middleCode middleCost checked outputMemory
      (seedBase+seedRows) lo compact j rest s E₀ extra
      (fun out=>(∀i v,i<((chart).rows history_).length→(honest).path.selections[i]?=some v→
        (out (capture+i)).val=selectionCount G v) ∧
        (accepted→(honest).path.savedRotations oldReel matrixEnd tail out) ∧ extraReads out)
  let carried (outputMemory : Memory w) : Prop :=
    (∃ v,which_=some v) → (honest).path.Held head outputMemory
  have paidAt : recorded (postBook pre) := (congrArg recorded same).mp paid
  have heldAt : carried (postBook pre) := (congrArg carried same).mp held
  refine ⟨?_,?_⟩
  · exact wide_held_from_original (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (payloadBits:=payloadBits) (fit:=fit) (begin_:=censusBase) (rom:=rom)
      (peer:=peerBank) (old:=wingBank) (org:=lookupBase) (homes:=dateHomes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=upperFence) (count:=countSlot) (plan:=freshReel) (all:=all) (m:=bookImage_) (original:=original) (middle:=middleCode)
      (cost:=middleCost) (arity:=arity) (groups:=groups) (stride:=stride) (oldTags:=oldTags) (K:=K) geometry oldReel capture matrixEnd (fun _=>rfl) later rfl space paidAt heldAt
  · intro c₀ chosen
    have dec:(chart).read history_=some c₀:=((DescentExteriorShelf.proposed_eq ..).mp chosen).1
    have written:history_=(chart).store c₀:=((chart).read_iff _ _).mp dec
    have followed : c₀=chosen_ :=
      ((congrArg (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow written).trans
        ((normalizedRoute X G S ordinary reset branch positive room shorten w fit).stored c₀)).symm
    refine ⟨⟨paidAt.original,paidAt.columns,?_,paidAt.appendix⟩,geometry⟩
    let rotationsAt (choice : (last).Choice) := (issued X G S ordinary reset branch positive room shorten choice).path.savedRotations
      freshReel upperFence tail (postBook pre)
    exact (congrArg rotationsAt followed).mpr
      ((honest).path.saved_late oldReel matrixEnd (paidAt.observed.2.1 ⟨_,dec⟩) later space)

theorem scheduled_wide_native (bins:W=NativeBranch.binLimit (k:=k) S) (geometry:room_)
    (later:matrixEnd≤upperFence) (space:upperFence+S.length+1<2^w)
    {extraReads:Memory w→Prop}
    (paid:DescentTerminalFundedReadback.Receipt originalMid originalCost checked postEntry_
      (seedBase+seedRows) lo compact j rest s E₀ extra
      (fun out=>(∀i v,i<((chart).rows history_).length→(honest).path.selections[i]?=some v→
        (out (capture+i)).val=selectionCount G v) ∧
        (accepted→(honest).path.savedRotations oldReel matrixEnd tail out) ∧ extraReads out))
    (held:(∃v,which_=some v)→(honest).path.Held head postEntry_) : flight_ ∧ capturedRows_ := by
  exact scheduled_wide_native_at (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch)
    (positive:=positive) (room:=room) (shorten:=shorten) (base:=base) (width:=width)
    (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords)
    (headerRows:=headerRows) (paidRows:=paidRows) (payloadBits:=payloadBits) (fit:=fit) (rom:=rom)
    (other:=other) (lo:=lo) (packWidth:=packWidth) (all:=all) (head:=head) (original:=original)
    (board:=board) (dateAge:=dateAge) (dateDegree:=dateDegree) (datePayload:=datePayload)
    (ordinaryAt:=ordinaryAt) (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes)
    (previousDate:=previousDate) (priorAddress:=priorAddress) (rosterBank:=rosterBank)
    (datedFloor:=datedFloor) (replayBase:=replayBase) (matrixTable:=matrixTable) (dateTag:=dateTag)
    (dateRotation:=dateRotation) (snapshots:=snapshots) (roleBase:=roleBase) (datedMem:=datedMem)
    (replayRoom:=replayRoom) (capture:=capture) originalMid originalCost bins geometry later space paid held

local notation "primitiveLanes_" => DescentDatedSeedStartup.Primitive.paletteLanes G rot startup.seedWidth Z payloadBits k
local notation "initialSource_" => DescentPackedSeed.Primitive.Source.jobs X S.copies startup.seedWidth payloadBits
local notation "seedEnd_" => (DescentDatedSeedStartup.Input.nodeChart startup k bootHosts (S.groupCount 0)).seedEnd
  (DescentDatedSeedStartup.endAddress X startup bootHosts (S.groupCount 0) k)
local notation "initialBound_" => DescentDatedSeedStartup.Primitive.initialEnd X S.copies startup.seedWidth payloadBits k
  bootHosts (S.groupCount 0) primitiveLanes_ seedEnd_
local notation "started_" => completeImage G rot X (S.initialDigits ordinary.radix) hostsEnough startup startingHeader payloadBits Z checked
local notation "finalDate_" => DateCode.history datesAt started_ S.length
local notation "captured_" => DescentLowCountBook.output capture rowAddress finalDate_ (captureDates).length



/-- The declared program is executed once on all assignments. This constructor uses the
actual per-date instructions and readbacks on their reached history, then follows the
original early/asynchronous tape through the purchased terminal book. -/
theorem scheduled_wide_from_dates (bins:W=NativeBranch.binLimit (k:=k) S) (geometry:room_)
    (shopCount:(dateSpec).scalar.shops=(dateHardware).hosts)
    (addressRoom:(dateSpec).maskBase censusBase<2^w) (wordPositive:0<w) (alive:0<(dateSpec).scalar.shops)
    (priorMetadata:(dateOut).metadataEnd dateOrigin≤earlyFloor) (one:chunks (dateHardware).groups (dateHardware).lanes=1)
    (rank:∀t<S.length,∀b₀,snapshots.compact t=some b₀→b₀.Fits w ((dateCalendar).scratch sliceEnd))
    (roleEnd:roleBase+DescentTerminalRoleTables.count roleBankBits≤(dateSpec).cohortEnd censusBase)
    (layout:(dateSpec).Before censusBase paidBank actorBank wingBank peerBank (lookupPage).total (lookupPage).modulo
      dateHomes (lookupPage).boundaries)
    (paidRowsFit:∀b₀,(dateSpec).scalar.shops≤(paidBank b₀).size)
    (signedRows:∀b₀ j₀,(dateSpec).scalar.shops≤(wingBank b₀ j₀).size)
    (sourceWide:Fintype.card (honest).origin.raw.V≤bootHosts)
    (signedFit:DescentSignedCableCodec.width 3 256*startup.packedLanes≤w)
    (fieldsFit:startup.operandBits*startup.operandLanes≤w) (headerLow:startingHeader<startup.base)
    (sourceSpace:DescentPackedSeed.publicWords X+DescentDyadicSpan.span initialSource_≤ seedEnd_)
    (liveness:0<primitiveLanes_) (embed:payloadBits≤w) (bootRoom:initialBound_<2^w)
    (total:∀i<S.length,∀m₀,∃out,(datesAt i).Runs m₀ out) (dateCheap:∀i<S.length,(datesAt i).cheap)
    (floors:ℕ→ℕ) (order:∀i<S.length,startingHeader<floors i)
    (observed:(honest).path.dateReadbacks (DateCode.history datesAt started_) dateTag dateRotation countAt
      ((chart).rows history_).length accepted)
    (apartCount:∀i<S.length,countAt i≠startingHeader) (apartMatrix:∀i<S.length,dateRotation i≠startingHeader)
    (keepCount:∀j₀<S.length,∀i,S.length≥i→j₀< i→countAt j₀<floors i)
    (keepMatrix:∀j₀<S.length,∀i,S.length≥i→j₀< i→dateRotation j₀<floors i)
    (frame:∀i<S.length,∀a,a≠startingHeader→a<floors i→
      DateCode.history datesAt started_ (i+1) a=DateCode.history datesAt started_ i a)
    (batchFit:S.batch<2^w) (seedLeft:seedBase+seedRows<capture) (captureEnd:capture+(captureDates).length≤lo)
    (historyLow:lo≤compact) (archiveEnd:front+extra≤ startingHeader) (reelData:front+extra≤replayBase)
    (below:compact+32*DescentExteriorShelf.span j rest s datePorts≤replayBase)
    (locs:∀a∈captureDates,capture+(captureDates).length≤countAt a ∧ countAt a+1<2^w)
    (rotLo:∀a<S.length,capture+(captureDates).length≤dateRotation a) (rotHi:∀a<S.length,dateRotation a<replayBase)
    (earlyRoom:earlyFloor<2^w) (later:matrixEnd≤upperFence) (matrixRoom:upperFence+S.length+1<2^w)
    (headLow:head<replayBase) (headApart:head<capture ∨ capture+(captureDates).length≤head)
    (datedHeld:(∃v,which_=some v)→(honest).path.Held head finalDate_)
    (table:matrixTable=compact) (published:datedMem=captured_) : flight_ ∧ capturedRows_ := by
  subst matrixTable
  subst datedMem
  have bounds_:=geometry
  obtain ⟨_,_,digits_,_,fits_,next_,_⟩:=bounds_
  have initialRows:=Root.wideCounted_on X S.copies s payloadBits w seed lo G.C packWidth steps compact
    (DescentExterior.publicRows X original) (Sum.elim history_ past_) originalTape
    (fun _ h=>Root.append_low _ _ _ _ h) digits_ fits_ next_ le_rfl
  have printed:Loaded compact (fun _=>LinearEquiv.refl _ _) (DescentExterior.publicRows X original)
      (all ∘ DescentTerminalFullPins.history ∘ Sum.inr) checked:=initialRows.2.2.2.1
  have originalFits:compact+17*DescentExteriorShelf.span j rest s datePorts≤ startingHeader:=by
    change compact+17*DescentExteriorShelf.span j rest s datePorts+extra≤ startingHeader at archiveEnd
    omega
  have native:=Branch.original_funded_readback (X:=X) (G:=G) (S:=S) (base:=base) (j:=j) (rest:=rest) (t:=s) (roof:=replayBase) (tag:=dateTag)
    (rotation:=dateRotation) (loc:=countAt) (lo:=capture) («compact»:=compact) (op:=rot)
    (teams:=q) (drift:=R) (headerRows:=headerRows) (paidRows:=paidRows) (phase:=datePhase)
    (snapshots:=snapshots) (blocks:=blockCast) (shops:=shopCount) (roleBase:=roleBase) (peer:=peerBank)
    (paid:=paidBank) (actor:=actorBank) (signedBanks:=wingBank) (cohortRoom:=replayRoom)
    (geometryRoom:=addressRoom) (wordPositive:=wordPositive) (alive:=alive) (priorMetadata:=priorMetadata)
    (one:=one) (rank:=rank) (roleEnd:=roleEnd) (before:=layout) (paidRowsFit:=paidRowsFit) (signedRows:=signedRows)
    («b»:=honest) (hp:=positive) (width:=width) (wide:=sourceWide) (pub:=hostsEnough)
    (l:=startup) (header:=startingHeader) (payload:=payloadBits) («Z»:=Z)
    datesAt checked signedFit fieldsFit headerLow sourceSpace liveness embed bootRoom total
    ((chart).rows history_).length accepted (DescentExterior.publicRows X original)
    (all ∘ DescentTerminalFullPins.history ∘ Sum.inr) printed floors originalFits order observed
    apartCount apartMatrix keepCount keepMatrix frame batchFit (captureEnd.trans historyLow) below locs
    rotLo rotHi earlyRoom dateCheap (seedBase+seedRows) lo extra seedLeft captureEnd historyLow archiveEnd reelData
  have preserved (survives:∃v,which_=some v): (honest).path.Held head
      (Branch.postEarlyPreflightMemory X G S base ordinary.radix g p q R rot headerRows paidRows
        j rest s replayBase datePhase snapshots blockCast roleBase peerBank paidBank actorBank wingBank replayRoom
        (DescentExteriorMatrixUpdate.Calendar.earlyImage S k tail replayBase dateTag dateRotation j rest s datePorts compact captured_)) :=
    Branch.funded_preflight_held (X:=X) (G:=G) (S:=S) (base:=base) (j:=j) (rest:=rest) (t:=s) (roof:=replayBase) (tag:=dateTag)
    (rotation:=dateRotation) (loc:=countAt) (lo:=capture) («compact»:=compact) (op:=rot)
    (teams:=q) (drift:=R) (headerRows:=headerRows) (paidRows:=paidRows) (phase:=datePhase)
    (snapshots:=snapshots) (blocks:=blockCast) (shops:=shopCount) (roleBase:=roleBase) (peer:=peerBank)
    (paid:=paidBank) (actor:=actorBank) (signedBanks:=wingBank) (cohortRoom:=replayRoom)
    (geometryRoom:=addressRoom) (wordPositive:=wordPositive) (alive:=alive) (priorMetadata:=priorMetadata)
    (one:=one) (rank:=rank) (roleEnd:=roleEnd) (before:=layout) (paidRowsFit:=paidRowsFit) (signedRows:=signedRows)
      («b»:=honest) finalDate_ head (datedHeld survives) headLow headApart rotHi below earlyRoom
  exact scheduled_wide_native (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch)
    (positive:=positive) (room:=room) (shorten:=shorten) (base:=base) (width:=width)
    (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords)
    (headerRows:=headerRows) (paidRows:=paidRows) (payloadBits:=payloadBits) (fit:=fit) (rom:=rom)
    (other:=other) (lo:=lo) (packWidth:=packWidth) (all:=all) (head:=head) (original:=original)
    (board:=board) (dateAge:=dateAge) (dateDegree:=dateDegree) (datePayload:=datePayload)
    (ordinaryAt:=ordinaryAt) (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes)
    (previousDate:=previousDate) (priorAddress:=priorAddress) (rosterBank:=rosterBank)
    (datedFloor:=datedFloor) (replayBase:=replayBase) (matrixTable:=compact) (dateTag:=dateTag)
    (dateRotation:=dateRotation) (snapshots:=snapshots) (roleBase:=roleBase) (datedMem:=captured_)
    (replayRoom:=replayRoom) (hostsEnough:=hostsEnough) (startup:=startup)
    (startingHeader:=startingHeader) (datesAt:=datesAt) (capture:=capture) (countAt:=countAt)
    bins geometry later matrixRoom native preserved


local notation "mountedMid_" mount => ((DateCode.afterBoot bootCode datesAt S.length).seq
   (Branch.historyMountedReel X S replayBase dateTag dateRotation countAt capture matrixTable k tail j rest s w
     (Chronology.RoleMount.phase mount))).seq termCode
local notation "mountedCost_" mount => (DateCode.afterTicks bootCost datesAt S.length+
    (((4+11*(captureDates).length)+(Chronology.RoleMount.phase mount).ticks)+
      DescentExteriorMatrixUpdate.Calendar.earlyClock S k tail j rest s datePorts))+termCost

/-- Install the role lookup table on the captured memory before the exterior reel. The funded
terminal program reads that same mounted image and pays the installation time. -/
theorem mounted_scheduled_wide_from_dates (bins:W=NativeBranch.binLimit (k:=k) S) (geometry:room_)
    (shopCount:(dateSpec).scalar.shops=(dateHardware).hosts)
    (addressRoom:(dateSpec).maskBase censusBase<2^w) (wordPositive:0<w) (alive:0<(dateSpec).scalar.shops)
    (priorMetadata:(dateOut).metadataEnd dateOrigin≤earlyFloor) (one:chunks (dateHardware).groups (dateHardware).lanes=1)
    (rank:∀t<S.length,∀b₀,snapshots.compact t=some b₀→b₀.Fits w ((dateCalendar).scratch sliceEnd))
    (roleEnd:roleBase+DescentTerminalRoleTables.count roleBankBits≤(dateSpec).cohortEnd censusBase)
    (layout:(dateSpec).Before censusBase paidBank actorBank wingBank peerBank (lookupPage).total (lookupPage).modulo
      dateHomes (lookupPage).boundaries)
    (paidRowsFit:∀b₀,(dateSpec).scalar.shops≤(paidBank b₀).size)
    (signedRows:∀b₀ j₀,(dateSpec).scalar.shops≤(wingBank b₀ j₀).size)
    (sourceWide:Fintype.card (honest).origin.raw.V≤bootHosts)
    (signedFit:DescentSignedCableCodec.width 3 256*startup.packedLanes≤w)
    (fieldsFit:startup.operandBits*startup.operandLanes≤w) (headerLow:startingHeader<startup.base)
    (sourceSpace:DescentPackedSeed.publicWords X+DescentDyadicSpan.span initialSource_≤ seedEnd_)
    (liveness:0<primitiveLanes_) (embed:payloadBits≤w) (bootRoom:initialBound_<2^w)
    (total:∀i<S.length,∀m₀,∃out,(datesAt i).Runs m₀ out) (dateCheap:∀i<S.length,(datesAt i).cheap)
    (floors:ℕ→ℕ) (order:∀i<S.length,startingHeader<floors i)
    (observed:(honest).path.dateReadbacks (DateCode.history datesAt started_) dateTag dateRotation countAt
      ((chart).rows history_).length accepted)
    (apartCount:∀i<S.length,countAt i≠startingHeader) (apartMatrix:∀i<S.length,dateRotation i≠startingHeader)
    (keepCount:∀j₀<S.length,∀i,S.length≥i→j₀< i→countAt j₀<floors i)
    (keepMatrix:∀j₀<S.length,∀i,S.length≥i→j₀< i→dateRotation j₀<floors i)
    (frame:∀i<S.length,∀a,a≠startingHeader→a<floors i→
      DateCode.history datesAt started_ (i+1) a=DateCode.history datesAt started_ i a)
    (batchFit:S.batch<2^w) (seedLeft:seedBase+seedRows<capture) (captureEnd:capture+(captureDates).length≤lo)
    (historyLow:lo≤compact) (archiveEnd:front+extra≤ startingHeader) (reelData:front+extra≤replayBase)
    (below:compact+32*DescentExteriorShelf.span j rest s datePorts≤replayBase)
    (locs:∀a∈captureDates,capture+(captureDates).length≤countAt a ∧ countAt a+1<2^w)
    (rotLo:∀a<S.length,capture+(captureDates).length≤dateRotation a) (rotHi:∀a<S.length,dateRotation a<replayBase)
    (earlyRoom:earlyFloor<2^w) (later:matrixEnd≤upperFence) (matrixRoom:upperFence+S.length+1<2^w)
    (headLow:head<replayBase) (headApart:head<capture ∨ capture+(captureDates).length≤head)
    (datedHeld:(∃v,which_=some v)→(honest).path.Held head finalDate_)
    (table:matrixTable=compact) (mount : RoleMount w roleBase replayBase)
    (preRole : compact+32*DescentExteriorShelf.span j rest s datePorts≤roleBase)
    (rotRole : ∀i<S.length,dateRotation i<roleBase)
    (startupRole : startingHeader<roleBase) (headRole : head<roleBase)
    (published : datedMem=mount.phase.image captured_) :
    flightFor_ (mountedMid_ mount) (mountedCost_ mount) ∧ capturedRows_ := by
  subst matrixTable
  subst datedMem
  have bounds_:=geometry
  obtain ⟨_,_,digits_,_,fits_,next_,_⟩:=bounds_
  have initialRows:=Root.wideCounted_on X S.copies s payloadBits w seed lo G.C packWidth steps compact
    (DescentExterior.publicRows X original) (Sum.elim history_ past_) originalTape
    (fun _ h=>Root.append_low _ _ _ _ h) digits_ fits_ next_ le_rfl
  have printed:Loaded compact (fun _=>LinearEquiv.refl _ _) (DescentExterior.publicRows X original)
      (all ∘ DescentTerminalFullPins.history ∘ Sum.inr) checked:=initialRows.2.2.2.1
  have originalFits:compact+17*DescentExteriorShelf.span j rest s datePorts≤ startingHeader:=by
    change compact+17*DescentExteriorShelf.span j rest s datePorts+extra≤ startingHeader at archiveEnd
    omega
  have native:=Branch.mounted_original_funded_readback (X:=X) (G:=G) (S:=S) (base:=base) (j:=j) (rest:=rest) (t:=s) (roof:=replayBase) (tag:=dateTag)
    (rotation:=dateRotation) (loc:=countAt) (lo:=capture) («compact»:=compact) (op:=rot)
    (teams:=q) (drift:=R) (headerRows:=headerRows) (paidRows:=paidRows) (phase:=datePhase)
    (snapshots:=snapshots) (blocks:=blockCast) (shops:=shopCount) (roleBase:=roleBase) (peer:=peerBank)
    (paid:=paidBank) (actor:=actorBank) (signedBanks:=wingBank) (cohortRoom:=replayRoom)
    (geometryRoom:=addressRoom) (wordPositive:=wordPositive) (alive:=alive) (priorMetadata:=priorMetadata)
    (one:=one) (rank:=rank) (roleEnd:=roleEnd) (before:=layout) (paidRowsFit:=paidRowsFit) (signedRows:=signedRows)
    («b»:=honest) (hp:=positive) (width:=width) (wide:=sourceWide) (pub:=hostsEnough)
    (l:=startup) (header:=startingHeader) (payload:=payloadBits) («Z»:=Z)
    datesAt checked signedFit fieldsFit headerLow sourceSpace liveness embed bootRoom total
    ((chart).rows history_).length accepted (DescentExterior.publicRows X original)
    (all ∘ DescentTerminalFullPins.history ∘ Sum.inr) printed floors originalFits order observed
    apartCount apartMatrix keepCount keepMatrix frame batchFit (captureEnd.trans historyLow) below locs
    rotLo rotHi earlyRoom dateCheap (seedBase+seedRows) lo extra seedLeft captureEnd historyLow archiveEnd reelData
    mount preRole rotRole startupRole
  have preserved (survives:∃v,which_=some v): (honest).path.Held head
      (Branch.postEarlyPreflightMemory X G S base ordinary.radix g p q R rot headerRows paidRows
        j rest s replayBase datePhase snapshots blockCast roleBase peerBank paidBank actorBank wingBank replayRoom
        (DescentExteriorMatrixUpdate.Calendar.earlyImage S k tail replayBase dateTag dateRotation j rest s datePorts compact (mount.phase.image captured_))) :=
    Branch.mounted_funded_preflight_held (X:=X) (G:=G) (S:=S) (base:=base) (j:=j) (rest:=rest) (t:=s) (roof:=replayBase) (tag:=dateTag)
    (rotation:=dateRotation) (loc:=countAt) (lo:=capture) («compact»:=compact) (op:=rot)
    (teams:=q) (drift:=R) (headerRows:=headerRows) (paidRows:=paidRows) (phase:=datePhase)
    (snapshots:=snapshots) (blocks:=blockCast) (shops:=shopCount) (roleBase:=roleBase) (peer:=peerBank)
    (paid:=paidBank) (actor:=actorBank) (signedBanks:=wingBank) (cohortRoom:=replayRoom)
    (geometryRoom:=addressRoom) (wordPositive:=wordPositive) (alive:=alive) (priorMetadata:=priorMetadata)
    (one:=one) (rank:=rank) (roleEnd:=roleEnd) (before:=layout) (paidRowsFit:=paidRowsFit) (signedRows:=signedRows)
      («b»:=honest) finalDate_ head (datedHeld survives) headLow headApart rotHi below earlyRoom mount headRole
  exact scheduled_wide_native_at (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch)
    (positive:=positive) (room:=room) (shorten:=shorten) (base:=base) (width:=width)
    (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords)
    (headerRows:=headerRows) (paidRows:=paidRows) (payloadBits:=payloadBits) (fit:=fit) (rom:=rom)
    (other:=other) (lo:=lo) (packWidth:=packWidth) (all:=all) (head:=head) (original:=original)
    (board:=board) (dateAge:=dateAge) (dateDegree:=dateDegree) (datePayload:=datePayload)
    (ordinaryAt:=ordinaryAt) (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes)
    (previousDate:=previousDate) (priorAddress:=priorAddress) (rosterBank:=rosterBank)
    (datedFloor:=datedFloor) (replayBase:=replayBase) (matrixTable:=compact) (dateTag:=dateTag)
    (dateRotation:=dateRotation) (snapshots:=snapshots) (roleBase:=roleBase) (datedMem:=mount.phase.image captured_)
    (replayRoom:=replayRoom) (capture:=capture) _ _ bins geometry later matrixRoom native preserved


/- The following large dependent telescope types have direct named consumers. -/
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "scheduled_wide_native_at"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "scheduled_wide_native"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "scheduled_wide_from_dates"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "mounted_scheduled_wide_from_dates"




end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

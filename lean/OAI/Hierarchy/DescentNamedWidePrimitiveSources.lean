import OAI.Hierarchy.DescentNamedLeafCoordinates
import OAI.Hierarchy.DescentNamedPostEarlyPreflight
import OAI.Hierarchy.DescentTerminalPrimitivePrivateFields
import OAI.Hierarchy.DescentNamedWideFlightSources
import OAI.Hierarchy.DescentNamedScheduledRasters

namespace OAI
/-! # The observed wide inputs on the physically scheduled primitive page -/
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
local notation "sourcePrimitiveImage" => (dateSpec).primitiveSnapshot (base:=censusBase) (w:=w) (q:=q) («p»:=p) (nd:=atomBits)
  (nodes:=nodeCap) (hidden:=cap) (args:=cap) (oldPaid:=paidBank) (actor:=actorBank) (first:=roleBanks) (second:=arityBanks)
  («chart»:=operandChart) (f0:=publicCell) (f7:=privateCell) ((lookupPage).image dateEntry)
local notation "datedDecoder" => Branch.decodeBook S G base ordinary.radix p q 3
  (dateSpec).cap (dateSpec).printBits (by decide)
local notation "sourceBookImage" => (dateSpec).bookSnapshot (base:=censusBase) (peer:=peerBank) (wing:=wingBank)
  (w:=w) (q:=q) («p»:=p) (nd:=atomBits) (nodes:=nodeCap) (hidden:=cap) (args:=cap)
  (oldPaid:=paidBank) (actor:=actorBank) (first:=roleBanks) (second:=arityBanks) («chart»:=operandChart)
  (f0:=publicCell) (f7:=privateCell) (decode:=datedDecoder) ((lookupPage).image dateEntry)
local notation "dateHomes" => (dateCalendar).homes sliceEnd
local notation "postEntry_" => Branch.postEarlyPreflightMemory X G S base ordinary.radix g p q R rot headerRows paidRows
  j rest s replayBase datePhase snapshots blockCast roleBase peerBank paidBank actorBank wingBank replayRoom
  (earlyImage datedMem)
local notation "bookControl" x:arg => portTable (G:=4) («V»:=(x).vertices) («M»:=(x).vertices*(x).arguments)
  (A:=(x).arguments) (a:=Book.tokenBits ((x).vertices*(x).arguments)) q
local notation "postBook" x:arg => (x).afterSiteControls censusBase q p peerBank wingBank
  (((x).scanPages lookupBase q).total) (((x).scanPages lookupBase q).modulo) dateHomes
  (((x).scanPages lookupBase q).boundaries)
  (((x).controls censusBase).after (bookControl x) (Book.expression ((x).parts censusBase)) sourceBookImage)

/-- The primitive fields at the end of the funded reset, replay and primitive printer. -/
def nativePrimitive : Memory w := sourcePrimitiveImage




/-- The first six Book columns issued from those actual primitive fields. -/
def nativeBooks : Memory w := sourceBookImage

/-- The register used by the Book scanner starts with the genuine weight sweep. -/
theorem native_books_at_primitive :
    sourceBookImage=(dateSpec).bookAtPrimitive censusBase peerBank wingBank datedDecoder sourcePrimitiveImage := rfl

/-- The complete post-early preflight uses the same Book memory, three scan tables,
replayed homes, control ports, and header draft as the original funded machine. -/
theorem native_post_early_books : postEntry_ = postBook dateSpec := rfl

/-- The wide checker uses exactly the funded dyadic bin count from epoch calibration. -/
theorem native_post_early_wide_books (bins : W=NativeBranch.binLimit (k:=k) S) :
    postEntry_=postBook pre := by
  subst W
  rfl

theorem native_wide_books_at_primitive (bins : W=NativeBranch.binLimit (k:=k) S) :
    sourceBookImage=(pre).bookAtPrimitive censusBase peerBank wingBank
      (Branch.decodeBook S G base ordinary.radix p q (pre).degree (pre).cap (pre).printBits (by change 3+1≤4; decide))
      sourcePrimitiveImage := by
  subst W
  rfl

local notation "primitiveImage_" => (@nativePrimitive F _ cp P X G S k cut tail n h C f g W q piece reset j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateTag dateRotation snapshots roleBase datedMem replayRoom)
local notation "bookImage_" => (@nativeBooks F _ cp P X G S k cut tail n h C f g W q piece ordinary reset j rest base headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateTag dateRotation snapshots roleBase datedMem replayRoom)

private def dateRowTarget := (b).target
local notation "rowTarget" => dateRowTarget X G S ordinary reset branch positive room shorten c
local notation "liveGrid" => (rowTarget).placement
local notation "liveHosts" => (rowTarget).vertex.trans (Fin.castLEEmb (rowTarget).valid.host)
local notation "dateMasks" => Venue.actual liveGrid (Function.Embedding.refl _) liveHosts
section DateRowFields
attribute [local irreducible] dateRowTarget

private def datedRowsRoster (raw : Fin H₀→Fin (rowTarget).placement.degree→Option (Fin H₀)) : Prop :=
  raw=(rowTarget).terminalRoster (rowTarget).valid.host

private def datedRowsPaidPrecision : Prop :=
  (dateVenue).paidBits=S.censusBits p

private def datedRowsWordRoom : Prop :=
  (dateSpec).maskBase censusBase<2^w

private def datedRowsSignedWidth : Prop :=
  (dateVenue).signedLanes=S.groupCount S.length

private def datedRowsRoleTable : Prop :=
  roleBase+DescentTerminalRoleTables.count roleBankBits≤replayBase

private def datedRowsTailRoom : Prop :=
  (dateMachine).fullEnd datedFloor≤replayBase

private def datedRowsReturned : Prop :=
  ∃ limit:ℕ,
    (Chronology.DatePorts.reset dateMachine ((dateMachine).stageStart datedFloor) dateInput).held
      (rowTarget) limit datedMem ∧
    ∀x,Reads (actorBank x) (dateMasks x) (S.groupCount S.length) datedMem

/-- Physical date and memory bounds for the reader's genuine roster. All incoming
signed entries come from the reached venue and the same paid actor pages. -/
structure PrimitiveDateRows (raw : Fin H₀→Fin (rowTarget).placement.degree→Option (Fin H₀)) : Prop where
  roster : @datedRowsRoster F _ cp P X G S k cut tail n h C f g W piece ordinary reset branch positive room shorten
    c raw
  lastDate : dateAge+1=S.length
  previousBlocks : previousDate.k=k
  paidPrecision : @datedRowsPaidPrecision F _ G S k cut tail n h C f g W piece reset boardDegree board dateAge dateDegree
    datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
  wordRoom : @datedRowsWordRoom F _ cp P X G S k cut tail n h C f g W q piece reset j rest headerRows paidRows w
    boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate
    priorAddress rosterBank datedFloor replayBase snapshots
  positiveWord : 0<w
  occupied : 0<dateShops
  rotations : ∀i<S.length,dateRotation i<replayBase
  matrix : matrixTable+32*DescentExteriorShelf.span j rest s datePorts≤replayBase
  signedWidth : @datedRowsSignedWidth F _ G S k cut tail n h C f g W piece reset boardDegree board dateAge dateDegree
    datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
  snapshotsFit : ∀t<S.length,∀bank,snapshots.compact t=some bank→bank.Fits w replayBase
  roleTable : @datedRowsRoleTable F _ cp P X G S k cut tail n h C f g W q piece reset headerRows paidRows replayBase
    roleBase
  tailRoom : @datedRowsTailRoom F _ G S k cut tail n h C f g W piece reset boardDegree board dateAge dateDegree
    datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
    replayBase
  returned : @datedRowsReturned F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room
    shorten c headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes
    primitiveLanes previousDate priorAddress rosterBank datedFloor datedMem dateInput

end DateRowFields

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

private theorem actor_channels {d d' blocks c c':ℕ} (left:d=d') (right:c=c') (rack:Rasters d' blocks c') :
    (presented left right rack).geometry=rack.geometry := by subst d';subst c';rfl

set_option maxHeartbeats 8000000 in
/-- The actual wide primitive snapshot retains the final register's complete actor mask.
Each test ranges over all graph sites at this host, group and block. -/
theorem native_acquired_actor_words {rawPeers} (date : physicalRows rawPeers) (printed : 2^(dateSpec).printBits<2^w) :
    ∀(i:Fin H₀)(x:DescentColonies.Block k),primitiveImage_ ((((dateSpec).channels censusBase).occupied x).base+i.val)=
      ((encode 1 groupsAt (dateMasks x i)).val:Computability.VPVNP.BurstRAM.Word w) := by
  let returned := date.returned
  have held := returned.choose_spec.1
  have actorsAt := returned.choose_spec.2
  have observed := Branch.scheduled_held_venue (X:=X) (g:=g) («p»:=p) (f:=f) (G:=G) (S:=S) (board:=board)
    (age:=dateAge) (degree:=dateDegree) (payload:=datePayload) (ordinary:=ordinaryAt)
    (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previous:=previousDate)
    (addr:=priorAddress) (oldRoster:=rosterBank) (floor:=datedFloor) (drift:=R) (op:=rot)
    («b»:=b) (radix:=ordinary.radix) («last»:=date.lastDate) (oldK:=date.previousBlocks)
    dateInput datedMem held
  have reads := (Branch.scheduled_occupation_words (tags:=0) (X:=X) (G:=G) (S:=S) (baseGroups:=reset.base) (radix:=ordinary.radix)
    (q:=q) («p»:=p) (g:=g) (drift:=R) (op:=rot) (headerRows:=headerRows) (paidRows:=paidRows)
    (board:=board) (age:=dateAge) (f:=f) (degree:=dateDegree) (payload:=datePayload) (ordinary:=ordinaryAt)
    (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previous:=previousDate) (addr:=priorAddress)
    (oldRoster:=rosterBank) (floor:=datedFloor) (j:=j) (r:=rest) (t:=s) (base:=replayBase)
    («compact»:=matrixTable) (tag:=dateTag) (rotation:=dateRotation) (A:=snapshots) (roleBase:=roleBase)
    (room:=replayRoom) («b»:=b) (u:=earlierPages) (m:=datedMem) («last»:=date.lastDate) (oldK:=date.previousBlocks)
    (word:=date.wordRoom) (positive:=date.positiveWord) (alive:=date.occupied) (prev:=date.rotations)
    (seed:=date.matrix) (signedPitch:=date.signedWidth) (rank:=date.snapshotsFit) (roleEnd:=date.roleTable)
    date.tailRoom observed actorsAt printed).1
  have rackEq := actor_channels (Branch.preflight_caps (tail:=tail) X G S b
    (Branch.geometryFormat G S k g p tail q R rot headerRows paidRows)).1
    (Branch.preflight_caps (tail:=tail) X G S b (Branch.geometryFormat G S k g p tail q R rot headerRows paidRows)).2.1
    ((dateSpec).rasters censusBase peerBank wingBank)
  intro i x
  exact (congrArg (fun rack : MaskAllocation.Channels (2^k) =>
    primitiveImage_ ((rack.occupied x).base + i.val)) rackEq.symm).trans (reads i x)

set_option maxHeartbeats 3000000 in
include age in
/-- Decode f1 on the actual primitive image using the physical stage's paid counts and the
already acquired exterior cohort totals. -/
theorem native_acquired_population_word {rawPeers} (date : physicalRows rawPeers)
    (precision:(dateVenue).paidBits=S.censusBits p) (acquired:paidPackets_) :
    ∀v,digit (Nat.clog 2 (nodeCap+1)) ((liveGrid).pos v).1.val
      (primitiveImage_ ((((dateSpec).channels censusBase).primitive ((liveGrid).block v) 3).base+((b).target.home v).val)).val=
      Fintype.card ((Branch.archive X G S b positive).bit.recipe v).Node := by
  obtain ⟨limit,held,actorsAt⟩:=date.returned
  have observed := Branch.scheduled_held_venue (X:=X) (g:=g) («p»:=p) (f:=f) (G:=G) (S:=S) (board:=board)
    (age:=dateAge) (degree:=dateDegree) (payload:=datePayload) (ordinary:=ordinaryAt)
    (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previous:=previousDate)
    (addr:=priorAddress) (oldRoster:=rosterBank) (floor:=datedFloor) (drift:=R) (op:=rot)
    («b»:=b) (radix:=ordinary.radix) («last»:=date.lastDate) (oldK:=date.previousBlocks)
    dateInput datedMem held
  exact Branch.scheduled_population_word (hp:=positive) (X:=X) (G:=G) (S:=S) (baseGroups:=base) (radix:=ordinary.radix)
    (q:=q) («p»:=p) (g:=g) (drift:=R) (op:=rot) (headerRows:=headerRows) (paidRows:=paidRows)
    (board:=board) (age:=dateAge) (f:=f) (degree:=dateDegree) (payload:=datePayload) (ordinary:=ordinaryAt)
    (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previous:=previousDate) (addr:=priorAddress)
    (oldRoster:=rosterBank) (floor:=datedFloor) (j:=j) (r:=rest) (t:=s) (base:=replayBase)
    («compact»:=matrixTable) (tag:=dateTag) (rotation:=dateRotation) (A:=snapshots) (roleBase:=roleBase)
    (room:=replayRoom) («b»:=b) (u:=earlierPages) (m:=datedMem) («last»:=date.lastDate) (oldK:=date.previousBlocks)
    (word:=date.wordRoom) (positive:=date.positiveWord) (alive:=date.occupied) (prev:=date.rotations)
    (seed:=date.matrix) (signedPitch:=date.signedWidth) (rank:=date.snapshotsFit) (roleEnd:=date.roleTable)
    date.tailRoom observed actorsAt precision age branch acquired.2.2.1

section PrivateRead
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
local notation "hiddenFit" => fun (i:Fin H₀) (v:Fin (Fintype.card ((homeOrd).Nodes i)))=>(DescentTerminalRestrictedRows.hidden_bound (trueLeaf).bit (trueLeaf).shape
  positive ((homeOrd).node i v)).trans ((trueLeaf).countsFit ((homeOrd).node i v))
local notation "nodeFit" => fun (i:Fin H₀) (v:Fin (Fintype.card ((homeOrd).Nodes i)))=>(trueLeaf).atoms ((homeOrd).node i v)
local notation "argFit" => fun (i:Fin H₀) (v:Fin (Fintype.card ((homeOrd).Nodes i))) u=>(((trueLeaf).shape ((homeOrd).node i v)).recipe_refs positive u).symm ▸
  (trueLeaf).refs ((homeOrd).node i v) u
local notation "realPage" => MaskAllocation.shelf (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) («p»:=p)
  (groups:=groupsAt) ((dateSpec).channels censusBase) ((dateSpec).maskBase censusBase)
variable (home:Fin (S.hostSize S.length)) (site:Fin (Fintype.card (((Branch.leafOrder X G S (issued X G S ordinary reset branch positive room shorten c) positive base width)).Nodes home)))
local notation "resident" => (homeOrd).node home site
local notation "argFitHere" u:arg => (((trueLeaf).shape resident).recipe_refs positive u).symm ▸ (trueLeaf).refs resident u
local notation "address_" => finProdFinEquiv (((b).target.placement.pos resident).1,(b).target.placement.block resident)
local notation "readAt" key:arg => venueField (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (cellAt (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) (DescentTerminalVertexFields.measured (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap)
  (w:=p) (groups:=groupsAt) realPage primitiveImage_ home) address_) key
local notation "nodeAt" u:arg => (ordinal ((liveRanks home).atom site) u).castLE (nodeFit home site)
local notation "wordAt" u:arg => (ordinal ((liveRanks home).hidden site) u).castLE (hiddenFit home site)
local notation "at_" => (liveRec home site)

/-- Reading the three occupied operand fields in the original dated image determines its
private count and every owned word width at the same native site and heap. -/
theorem native_private_fields (wordRoom:(dateSpec).maskBase censusBase<2^w)
    (dataRoom:groupsAt*actualSpan G S rot q p R≤w)
    (nodes:readAt nodeCount=Fintype.card (at_).Node)
    (arities:∀u,readAt (nodeArity (nodeAt u))=(at_).arity u)
    (references:∀u (a:Fin ((at_).arity u)),readAt (nodeArg (nodeAt u) (a.castLE (argFitHere u)))=
      ((at_).operand u a).elim (fun x=>x.val+1) (fun x=>q+(ordinal ((liveRanks home).hidden site) x).val+1)) :
    readAt hiddenCount=Fintype.card (at_).Hidden ∧
    ∀u,readAt (hiddenWidth (wordAt u))=(at_).width u:=by
  have chain:=(dateSpec).layers censusBase
  rcases chain with ⟨a,b₁,c₁,d,e,f₁,g₁,h₁,j₁⟩
  have lim:(dateSpec).scalar.finish ((dateSpec).primitive censusBase)<2^w:=by
    change (dateSpec).weights censusBase<2^w
    exact (c₁.trans (d.trans (e.trans (f₁.trans (g₁.trans (h₁.trans j₁)))))).trans_lt wordRoom
  have kit:=(dateSpec).scalar.realized ((dateSpec).primitive censusBase) ((dateSpec).population censusBase) _
    ((dateSpec).prior censusBase) lim (by change 0<3+nodeCap+4*(nodeCap*cap)+2*(dateSpec).cap;omega)
  have covers (f:Fin 3) : familySize (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
      (DescentTerminalPrivateSourceChannels.family f)*groupsAt≤(dateSpec).scalar.countBits:=by
    rw [Nat.mul_comm]
    apply (Finset.single_le_sum (f:=widthAt (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) groupsAt)
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ (DescentTerminalPrivateSourceChannels.family f))).trans
    rw [DescentTerminalVertexFields.volume]
    exact Nat.mul_le_mul_left _ (Nat.le_succ _)
  exact (dateSpec).scalar.private_fields ((dateSpec).primitive censusBase) ((dateSpec).population censusBase)
    ((dateSpec).scalar.subrow ((dateSpec).actors censusBase)) roleBanks arityBanks operandChart publicCell privateCell
    ((last).state c).graph positive homeOrd (trueLeaf).bit (trueLeaf).shape (allCodes).store (trueLeaf).birth
    home (liveRanks home) (hiddenFit home) (nodeFit home) (argFit home) (Branch.leaf_arity X G S b positive base width qFit home) site
    ((dateSpec).maskBase censusBase) _ ((b).target.placement.block resident) home ((b).target.placement.pos resident).1
    kit ((Nat.mul_le_mul_left groupsAt (Nat.le_succ _)).trans dataRoom) covers nodes arities references


/-- Only the three per-node fields and the paid node count have to be joined at the native
primitive date. The route, occupancy and node population are restored by the later measured read. -/
theorem native_operand_receipts (wordRoom:(dateSpec).maskBase censusBase<2^w)
    (dataRoom:groupsAt*actualSpan G S rot q p R≤w)
    (nodes:readAt nodeCount=Fintype.card (at_).Node)
    (roles:∀u,readAt (nodeRole (nodeAt u))=((at_).tag u).val+1)
    (arities:∀u,readAt (nodeArity (nodeAt u))=(at_).arity u)
    (references:∀u (a:Fin ((at_).arity u)),readAt (nodeArg (nodeAt u) (a.castLE (argFitHere u)))=
      ((at_).operand u a).elim (fun x=>x.val+1) (fun x=>q+(ordinal ((liveRanks home).hidden site) x).val+1)) :
    PrimitiveReceipts (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) ((homeOrd).site home) (liveRec home) (liveRanks home) (hiddenFit home)
      (nodeFit home) (argFit home) site (fun key=>readAt key) (fun _=>True):=by
  have counted : readAt hiddenCount=Fintype.card (at_).Hidden ∧
      ∀u,readAt (hiddenWidth (wordAt u))=(at_).width u:=by
    apply native_private_fields (home:=home) (site:=site) <;> assumption
  exact ⟨trivial,trivial,counted.1,trivial,counted.2,roles,arities,references⟩


/-- The paid node count at this resident is the population lane of the actual reached
site. The address is shared by the scheduled population printer and the scalar reader. -/
theorem native_acquired_population_field {rawPeers} (date:physicalRows rawPeers) (acquired:paidPackets_) :
    readAt nodeCount=Fintype.card (at_).Node :=by
  have here:(b).target.home resident=home:=(((homeOrd).nodes home).symm site).property
  let rack:DescentColonies.Block k:=(b).target.placement.block resident
  have sizes:=((dateSpec).prior censusBase).actorSize rack
  have bound := (congrArg (fun bank : Bank => bank.base + bank.size)
    (MaskAllocation.Channels.occupied_at ((dateSpec).channels censusBase) rack).symm).trans_le
    ((dateSpec).channels_before censusBase (finProdFinEquiv (rack,(0:Fin 9))))
  have hostRoom:H₀≤2^w:=sizes.trans ((Nat.le_add_left ..).trans (bound.trans date.wordRoom.le))
  apply DescentTerminalRolePrefix.population ((dateSpec).channels censusBase) _ primitiveImage_ rack home
    ((b).target.placement.pos resident).1 hostRoom
  · change H₀≤2^(Nat.clog 2 H₀)
    exact Nat.le_pow_clog (by decide) _
  · have read := native_acquired_population_word («F»:=F) («cp»:=cp) («P»:=P) («X»:=X) («G»:=G) («S»:=S)
      («k»:=k) («cut»:=cut) («tail»:=tail) («n»:=n) («h»:=h) («C»:=C)
      («f»:=f) («g»:=g) («W»:=W) («q»:=q) («piece»:=piece) («ordinary»:=ordinary)
      («reset»:=reset) («branch»:=branch) («positive»:=positive) («room»:=room) («shorten»:=shorten) («c»:=c)
      («j»:=j) («rest»:=rest) («base»:=base) («width»:=width) («age»:=age) («headerRows»:=headerRows)
      («paidRows»:=paidRows) («w»:=w) («boardDegree»:=boardDegree) («board»:=board) («dateAge»:=dateAge) («dateDegree»:=dateDegree)
      («datePayload»:=datePayload) («ordinaryAt»:=ordinaryAt) («operandLanes»:=operandLanes) («primitiveLanes»:=primitiveLanes) («previousDate»:=previousDate) («priorAddress»:=priorAddress)
      («rosterBank»:=rosterBank) («datedFloor»:=datedFloor) («replayBase»:=replayBase) («matrixTable»:=matrixTable) («dateTag»:=dateTag) («dateRotation»:=dateRotation)
      («snapshots»:=snapshots) («roleBase»:=roleBase) («datedMem»:=datedMem) («dateInput»:=dateInput) («replayRoom»:=replayRoom) (date:=date) date.paidPrecision acquired resident
    exact (congrArg (fun place : Fin H₀ => digit (Nat.clog 2 (nodeCap+1)) ((liveGrid).pos resident).1.val
      (primitiveImage_ ((((dateSpec).channels censusBase).primitive ((liveGrid).block resident) 3).base + place.val)).val) here).symm.trans read

private theorem primitiveCountFitsMask (spec : DescentTerminalPreflightSpace.Spec) (origin : ℕ)
    {bits : ℕ} (fit : spec.maskBase origin < 2^bits) : spec.scalar.countBits ≤ bits := by
  obtain ⟨_, _, weightBook, bookStop, controlStop, cableStop, literalStart, draftStart, maskStartBound⟩ := spec.layers origin
  exact spec.scalar.count_word_fits (spec.primitive origin) ((weightBook.trans (bookStop.trans (controlStop.trans (cableStop.trans (literalStart.trans (draftStart.trans maskStartBound)))))).trans_lt fit)

set_option maxHeartbeats 6500000 in
/-- At the original funded primitive date, only the role, arity and operands of live
nodes remain to supply the entire site record. -/
theorem native_acquired_operand_receipts {rawPeers} (date:physicalRows rawPeers) (acquired:paidPackets_)
    (roles:∀u,readAt (nodeRole (nodeAt u))=((at_).tag u).val+1)
    (arities:∀u,readAt (nodeArity (nodeAt u))=(at_).arity u)
    (references:∀u (a:Fin ((at_).arity u)),readAt (nodeArg (nodeAt u) (a.castLE (argFitHere u)))=
      ((at_).operand u a).elim (fun x=>x.val+1) (fun x=>q+(ordinal ((liveRanks home).hidden site) x).val+1)) :
    PrimitiveReceipts (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) ((homeOrd).site home) (liveRec home) (liveRanks home) (hiddenFit home)
      (nodeFit home) (argFit home) site (fun key=>readAt key) (fun _=>True):=by
  have dataRoom : groupsAt*actualSpan G S rot q p R ≤ w :=
    primitiveCountFitsMask (dateSpec) censusBase date.wordRoom
  apply native_operand_receipts («F»:=F) («cp»:=cp) («P»:=P) («X»:=X) («G»:=G) («S»:=S) («k»:=k)
      («cut»:=cut) («tail»:=tail) («n»:=n) («h»:=h) («C»:=C) («f»:=f) («g»:=g)
      («W»:=W) («q»:=q) («piece»:=piece) («ordinary»:=ordinary) («reset»:=reset) («branch»:=branch) («positive»:=positive)
      («room»:=room) («shorten»:=shorten) («c»:=c) («j»:=j) («rest»:=rest) («base»:=base) («width»:=width)
      («age»:=age) («wFit»:=wFit) («qFit»:=qFit) («qh»:=qh) («template»:=template) («sitesPositive»:=sitesPositive) («rawWords»:=rawWords)
      («headerRows»:=headerRows) («paidRows»:=paidRows) («pool»:=pool) («raw»:=raw) («w»:=w) («boardDegree»:=boardDegree) («board»:=board)
      («dateAge»:=dateAge) («dateDegree»:=dateDegree) («datePayload»:=datePayload) («ordinaryAt»:=ordinaryAt) («operandLanes»:=operandLanes) («primitiveLanes»:=primitiveLanes) («previousDate»:=previousDate)
      («priorAddress»:=priorAddress) («rosterBank»:=rosterBank) («datedFloor»:=datedFloor) («replayBase»:=replayBase) («matrixTable»:=matrixTable) («dateTag»:=dateTag) («dateRotation»:=dateRotation)
      («snapshots»:=snapshots) («roleBase»:=roleBase) («datedMem»:=datedMem) («replayRoom»:=replayRoom) («home»:=home) («site»:=site) (wordRoom:=date.wordRoom)
      (dataRoom:=dataRoom) (roles:=roles) (arities:=arities) (references:=references)
  exact native_acquired_population_field («F»:=F) («cp»:=cp) («P»:=P) («X»:=X) («G»:=G) («S»:=S) («k»:=k)
      («cut»:=cut) («tail»:=tail) («n»:=n) («h»:=h) («C»:=C) («f»:=f) («g»:=g)
      («W»:=W) («q»:=q) («piece»:=piece) («ordinary»:=ordinary) («reset»:=reset) («branch»:=branch) («positive»:=positive)
      («room»:=room) («shorten»:=shorten) («c»:=c) («j»:=j) («rest»:=rest) («base»:=base) («width»:=width)
      («age»:=age) («wFit»:=wFit) («qFit»:=qFit) («qh»:=qh) («template»:=template) («sitesPositive»:=sitesPositive) («rawWords»:=rawWords)
      («headerRows»:=headerRows) («paidRows»:=paidRows) («pool»:=pool) («raw»:=raw) («w»:=w) («boardDegree»:=boardDegree) («board»:=board)
      («dateAge»:=dateAge) («dateDegree»:=dateDegree) («datePayload»:=datePayload) («ordinaryAt»:=ordinaryAt) («operandLanes»:=operandLanes) («primitiveLanes»:=primitiveLanes) («previousDate»:=previousDate)
      («priorAddress»:=priorAddress) («rosterBank»:=rosterBank) («datedFloor»:=datedFloor) («replayBase»:=replayBase) («matrixTable»:=matrixTable) («dateTag»:=dateTag) («dateRotation»:=dateRotation)
      («snapshots»:=snapshots) («roleBase»:=roleBase) («datedMem»:=datedMem) («dateInput»:=dateInput) («replayRoom»:=replayRoom) («home»:=home) («site»:=site) date acquired


local notation "cellV" => (⟨q,allTags,cap,nodeCap,cap,p,groupsAt⟩:Home.Format)
local notation "cellVenues" => groupsAt*2^k
local notation "cellCodes" => DescentTerminalScalarHeader.range q allTags cap nodeCap cap p cellVenues
local notation "cellFront" => compact+17*DescentExteriorShelf.span j rest s datePorts
local notation "cellRoutes" => (RouteSources.Tables.mk 4 cellVenues (cellVenues*NativeBranch.localLimit G S)
  (NativeBranch.localLimit G S) (Book.tokenBits (cellVenues*NativeBranch.localLimit G S)) W q K)
local notation "cellInput" => (dateSpec).reachedInput censusBase rom q piece W K cellCodes cellFront peerBank wingBank
  (lookupPage).total (lookupPage).modulo dateHomes (lookupPage).boundaries cfg cellV other cellRoutes (dateSpec).vertices (dateSpec).pageBits
local notation "cells" => (dateSpec).channels censusBase
local notation "maskStart" => (dateSpec).maskBase censusBase
local notation "afterCount" => afterMeter cellV cfg cells maskStart
local notation "homeArena" => rowArena cfg cellInput afterCount
local notation "chipIn" => (dateSpec).chipInput censusBase rom q p peerBank wingBank (lookupPage).total
  (lookupPage).modulo dateHomes (lookupPage).boundaries cfg other
local notation "tableLiterals" => ScalarLiterals.data q allTags cap nodeCap cap p (dateSpec).vertices W (dateSpec).pageBits
  (cfg).terminal.pool qh ((cellRoutes).columns homeArena (chipIn).sources) ((cellRoutes).value (fun _ _=>0))
local notation "cellPlan" => AddressPlan.layout cfg cellInput afterCount (registers cellV cfg cells maskStart head)
variable (cellShort:((preflightSpec X G S k g (W*piece) tail (geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows))).vertices*DescentTerminalVertexFields.span q (DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))) (W*piece) (max 1 (max reset.bitsR (C*reset.bitsR)))) (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))) (S.epochPower^S.localTokenExponent) (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))) (W*piece)≤((preflightSpec X G S k g (W*piece) tail (geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows))).pageBits)
local notation "cellMem" => Suffix.sockets cfg cellPlan
  ((homeArena).mount (input cellV cfg cellInput cells maskStart head cellShort tableLiterals primitiveImage_))

set_option maxHeartbeats 8500000 in
/-- At the funded emitter sockets the original normalized record is still the one read by
the per-node role, arity and operand programs at this named physical venue. -/
theorem native_acquired_sockets_receipts {rawPeers} (date:physicalRows rawPeers) (acquired:paidPackets_)
    (boot:(dateSpec).Before censusBase paidBank actorBank wingBank peerBank
      (lookupPage).total (lookupPage).modulo dateHomes (lookupPage).boundaries)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(dateSpec).literalBase censusBase)
    (full:cellFront+DescentTerminalPublicIdentity.total K W q piece cellCodes (cfg).terminal.plane.rawRows (cfg).packets≤ maskStart)
    (space:AddressPlan.last cellV cfg cellInput cells maskStart<2^w)
    (roles:∀u,readAt (nodeRole (nodeAt u))=((at_).tag u).val+1)
    (arities:∀u,readAt (nodeArity (nodeAt u))=(at_).arity u)
    (references:∀u (a:Fin ((at_).arity u)),readAt (nodeArg (nodeAt u) (a.castLE (argFitHere u)))=
      ((at_).operand u a).elim (fun x=>x.val+1) (fun x=>q+(ordinal ((liveRanks home).hidden site) x).val+1)) :
  PrimitiveReceipts (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) ((homeOrd).site home) (liveRec home) (liveRanks home) (hiddenFit home)
      (nodeFit home) (argFit home) site (venueField (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (cellAt (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) (DescentTerminalVertexFields.measured (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap)
        (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) (meter cellV cells maskStart).layout cellMem home)
        ((b).target.rawResident homeOrd rfl home site))) (fun _=>True) := by
    have operandReceipts := native_acquired_operand_receipts («F»:=F) («cp»:=cp) («P»:=P) («X»:=X) («G»:=G) («S»:=S) («k»:=k)
      («cut»:=cut) («tail»:=tail) («n»:=n) («h»:=h) («C»:=C) («f»:=f) («g»:=g)
      («W»:=W) («q»:=q) («piece»:=piece) («ordinary»:=ordinary) («reset»:=reset) («branch»:=branch) («positive»:=positive)
      («room»:=room) («shorten»:=shorten) («c»:=c) («j»:=j) («rest»:=rest) («base»:=base) («width»:=width)
      («age»:=age) («wFit»:=wFit) («qFit»:=qFit) («qh»:=qh) («template»:=template) («sitesPositive»:=sitesPositive) («rawWords»:=rawWords)
      («headerRows»:=headerRows) («paidRows»:=paidRows) («pool»:=pool) («raw»:=raw) («w»:=w) («boardDegree»:=boardDegree) («board»:=board)
      («dateAge»:=dateAge) («dateDegree»:=dateDegree) («datePayload»:=datePayload) («ordinaryAt»:=ordinaryAt) («operandLanes»:=operandLanes) («primitiveLanes»:=primitiveLanes) («previousDate»:=previousDate)
      («priorAddress»:=priorAddress) («rosterBank»:=rosterBank) («datedFloor»:=datedFloor) («replayBase»:=replayBase) («matrixTable»:=matrixTable) («dateTag»:=dateTag) («dateRotation»:=dateRotation)
      («snapshots»:=snapshots) («roleBase»:=roleBase) («datedMem»:=datedMem) («dateInput»:=dateInput) («replayRoom»:=replayRoom) («home»:=home) («site»:=site)
      (date:=date) (acquired:=acquired)
      (roles:=roles) (arities:=arities) (references:=references)
    have early:=(dateSpec).earlier censusBase rom q piece W K cellCodes cellFront peerBank wingBank (lookupPage).total
      (lookupPage).modulo dateHomes (lookupPage).boundaries cfg cellV other cellRoutes (dateSpec).vertices
      (dateSpec).pageBits paidBank actorBank boot romTop full space
    have dataEq := AddressPlan.sockets_measured cellV cfg cellInput cells maskStart head cellShort
      tableLiterals primitiveImage_ early space ((dateSpec).channels_before censusBase) home
    let hasReceipts (data : BlockFields q allTags cap nodeCap cap p groupsAt (2^k)) : Prop :=
      PrimitiveReceipts (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) ((homeOrd).site home)
        (liveRec home) (liveRanks home) (hiddenFit home) (nodeFit home) (argFit home) site
        (venueField (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
          (cellAt (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt)
            (blocks:=2^k) data address_)) (fun _=>True)
    exact (congrArg hasReceipts dataEq).mpr operandReceipts

end PrivateRead




set_option maxHeartbeats 8000000 in
include qFit in
theorem native_acquired_public_words {rawPeers} (date:physicalRows rawPeers) (acquired:paidPackets_)
    (printed:2^(dateSpec).printBits<2^w) : ∀v,
      venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) (DescentTerminalVertexFields.measured (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
        (groups:=groupsAt) (blocks:=2^k) (MaskAllocation.shelf (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) («p»:=p) (groups:=groupsAt) (blocks:=2^k)
          (Branch.presented (Branch.preflight_caps (tail:=tail) X G S b (Branch.geometryFormat G S k g p tail q R rot headerRows paidRows)).1
            (Branch.preflight_caps (tail:=tail) X G S b (Branch.geometryFormat G S k g p tail q R rot headerRows paidRows)).2.1
              ((dateSpec).rasters censusBase peerBank wingBank)).geometry 0) primitiveImage_ (liveHosts ((liveGrid).pos v).2))
        (finProdFinEquiv (((liveGrid).pos v).1,(liveGrid).block v))) publicArity=
          DescentTerminalGraphRows.arity ((last).state c).graph p v := by
  let returned := date.returned
  have held := returned.choose_spec.1
  have actorsAt := returned.choose_spec.2
  have observed := Branch.scheduled_held_venue (X:=X) (g:=g) («p»:=p) (f:=f) (G:=G) (S:=S) (board:=board)
    (age:=dateAge) (degree:=dateDegree) (payload:=datePayload) (ordinary:=ordinaryAt)
    (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previous:=previousDate)
    (addr:=priorAddress) (oldRoster:=rosterBank) (floor:=datedFloor) (drift:=R) (op:=rot)
    («b»:=b) (radix:=ordinary.radix) («last»:=date.lastDate) (oldK:=date.previousBlocks)
    dateInput datedMem held
  exact (Branch.scheduled_venue_public (tags:=tagCount) (hp:=positive) (X:=X) (G:=G) (S:=S) (baseGroups:=base) (radix:=ordinary.radix)
    (q:=q) («p»:=p) (g:=g) (drift:=R) (op:=rot) (headerRows:=headerRows) (paidRows:=paidRows)
    (board:=board) (age:=dateAge) (f:=f) (degree:=dateDegree) (payload:=datePayload) (ordinary:=ordinaryAt)
    (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previous:=previousDate) (addr:=priorAddress)
    (oldRoster:=rosterBank) (floor:=datedFloor) (j:=j) (r:=rest) (t:=s) (base:=replayBase)
    («compact»:=matrixTable) (tag:=dateTag) (rotation:=dateRotation) (A:=snapshots) (roleBase:=roleBase)
    (room:=replayRoom) («b»:=b) (u:=earlierPages) (m:=datedMem) («last»:=date.lastDate) (oldK:=date.previousBlocks)
    (word:=date.wordRoom) (positive:=date.positiveWord) (alive:=date.occupied) (prev:=date.rotations)
    (seed:=date.matrix) (signedPitch:=date.signedWidth) (rank:=date.snapshotsFit) (roleEnd:=date.roleTable)
    date.tailRoom observed actorsAt printed).2 qFit acquired.2.2.2

local notation "inputsAt_" O:arg H:arg Q:arg => datedRowsWith O H Q physicalRows
local notation "trueRoster" => (b).target.terminalRoster (b).target.valid.host
local notation "ownsRoster" => fun raw => raw=trueRoster
local notation "inputs_" => inputsAt_ org homes m
local notation "published_" => publishedAt_ org homes m

/-- The acquired site words and widths at the real Book and primitive buffers,
with the actual terminal roster used for their peer keys. -/
def WideEarnedSitePages : Prop := datedRowsChecked lookupBase dateHomes bookImage_ ownsRoster (fun _:Prop=>True) (fun _:Prop=>True) (fun _:Prop=>True)

/-- The final scheduled register on the same roster and assignment. -/
def WideRegisteredDateRows : Prop := physicalRows trueRoster

set_option maxHeartbeats 7500000 in
theorem wide_earned_from_registered (actual : physicalRows trueRoster) (captured : paidCapture_) (packets : paidPackets_)
    (sites : datedRowsChecked lookupBase dateHomes bookImage_ ownsRoster (fun _:Prop=>True) (fun _:Prop=>True) (fun _:Prop=>True)) :
    inputsAt_ lookupBase dateHomes bookImage_ := by
  have carry : ∀rs,(ownsRoster) rs→physicalRows rs := by
    intro rs same
    exact same.symm ▸ actual
  apply wide_source_rows_mono («F»:=F) («cp»:=cp) («P»:=P) («X»:=X) («G»:=G) («S»:=S) («k»:=k)
      («cut»:=cut) («tail»:=tail) («n»:=n) («h»:=h) («C»:=C) («f»:=f) («g»:=g)
      («W»:=W) («q»:=q) («piece»:=piece) («ordinary»:=ordinary) («reset»:=reset) («branch»:=branch) («positive»:=positive)
      («room»:=room) («shorten»:=shorten) («c»:=c) («j»:=j) («rest»:=rest) («base»:=base) («width»:=width)
      («age»:=age) («wFit»:=wFit) («qFit»:=qFit) («qh»:=qh) («template»:=template) («sitesPositive»:=sitesPositive) («rawWords»:=rawWords)
      («headerRows»:=headerRows) («paidRows»:=paidRows) («pool»:=pool) («raw»:=raw) («w»:=w) («K»:=K) («payloadBits»:=payloadBits)
      («fit»:=fit) («begin_»:=censusBase) («rom»:=rom) («peer»:=peerBank) («old»:=wingBank) («org»:=lookupBase) («homes»:=dateHomes)
      («other»:=other) («arity»:=arity) («groups»:=groups) («stride»:=stride) («oldTags»:=oldTags) («codec»:=codec) («lo»:=lo)
      («packWidth»:=packWidth) («all»:=all) («head»:=head) («short»:=short) («fence»:=fence) («count»:=count) («plan»:=plan)
      («primitive»:=primitiveImage_) («m»:=bookImage_) («original»:=original) carry
  apply wide_restore_native_counts («F»:=F) («cp»:=cp) («P»:=P) («X»:=X) («G»:=G) («S»:=S) («k»:=k)
      («cut»:=cut) («tail»:=tail) («n»:=n) («h»:=h) («C»:=C) («f»:=f) («g»:=g)
      («W»:=W) («q»:=q) («piece»:=piece) («ordinary»:=ordinary) («reset»:=reset) («branch»:=branch) («positive»:=positive)
      («room»:=room) («shorten»:=shorten) («c»:=c) («j»:=j) («rest»:=rest) («base»:=base) («width»:=width)
      («age»:=age) («wFit»:=wFit) («qFit»:=qFit) («qh»:=qh) («template»:=template) («sitesPositive»:=sitesPositive) («rawWords»:=rawWords)
      («headerRows»:=headerRows) («paidRows»:=paidRows) («pool»:=pool) («raw»:=raw) («w»:=w) («K»:=K) («payloadBits»:=payloadBits)
      («fit»:=fit) («begin_»:=censusBase) («rom»:=rom) («peer»:=peerBank) («old»:=wingBank) («org»:=lookupBase) («homes»:=dateHomes)
      («other»:=other) («arity»:=arity) («groups»:=groups) («stride»:=stride) («oldTags»:=oldTags) («codec»:=codec) («lo»:=lo)
      («packWidth»:=packWidth) («all»:=all) («head»:=head) («short»:=short) («fence»:=fence) («count»:=count) («plan»:=plan)
      («primitive»:=primitiveImage_) («m»:=bookImage_) («original»:=original) (ports:=native_acquired_public_words («F»:=F) («cp»:=cp) («P»:=P) («X»:=X) («G»:=G) («S»:=S) («k»:=k)
      («cut»:=cut) («tail»:=tail) («n»:=n) («h»:=h) («C»:=C) («f»:=f) («g»:=g)
      («W»:=W) («q»:=q) («piece»:=piece) («ordinary»:=ordinary) («reset»:=reset) («branch»:=branch) («positive»:=positive)
      («room»:=room) («shorten»:=shorten) («c»:=c) («j»:=j) («rest»:=rest) («base»:=base) («width»:=width)
      («qFit»:=qFit) («headerRows»:=headerRows) («paidRows»:=paidRows) («w»:=w) («arity»:=arity) («groups»:=groups) («stride»:=stride)
      («oldTags»:=oldTags) («boardDegree»:=boardDegree) («board»:=board) («dateAge»:=dateAge) («dateDegree»:=dateDegree) («datePayload»:=datePayload) («ordinaryAt»:=ordinaryAt)
      («operandLanes»:=operandLanes) («primitiveLanes»:=primitiveLanes) («previousDate»:=previousDate) («priorAddress»:=priorAddress) («rosterBank»:=rosterBank) («datedFloor»:=datedFloor) («replayBase»:=replayBase)
      («matrixTable»:=matrixTable) («dateTag»:=dateTag) («dateRotation»:=dateRotation) («snapshots»:=snapshots) («roleBase»:=roleBase) («datedMem»:=datedMem) («dateInput»:=dateInput)
      («replayRoom»:=replayRoom) actual packets) (population:=native_acquired_population_word («F»:=F) («cp»:=cp) («P»:=P) («X»:=X) («G»:=G) («S»:=S) («k»:=k)
      («cut»:=cut) («tail»:=tail) («n»:=n) («h»:=h) («C»:=C) («f»:=f) («g»:=g)
      («W»:=W) («q»:=q) («piece»:=piece) («ordinary»:=ordinary) («reset»:=reset) («branch»:=branch) («positive»:=positive)
      («room»:=room) («shorten»:=shorten) («c»:=c) («j»:=j) («rest»:=rest) («base»:=base) («width»:=width)
      («age»:=age) («headerRows»:=headerRows) («paidRows»:=paidRows) («w»:=w) («boardDegree»:=boardDegree) («board»:=board) («dateAge»:=dateAge)
      («dateDegree»:=dateDegree) («datePayload»:=datePayload) («ordinaryAt»:=ordinaryAt) («operandLanes»:=operandLanes) («primitiveLanes»:=primitiveLanes) («previousDate»:=previousDate) («priorAddress»:=priorAddress)
      («rosterBank»:=rosterBank) («datedFloor»:=datedFloor) («replayBase»:=replayBase) («matrixTable»:=matrixTable) («dateTag»:=dateTag) («dateRotation»:=dateRotation) («snapshots»:=snapshots)
      («roleBase»:=roleBase) («datedMem»:=datedMem) («dateInput»:=dateInput) («replayRoom»:=replayRoom) (date:=actual) actual.paidPrecision packets)
    (sourceData:=wide_restore_capture («F»:=F) («cp»:=cp) («P»:=P) («X»:=X) («G»:=G) («S»:=S) («k»:=k)
      («cut»:=cut) («tail»:=tail) («n»:=n) («h»:=h) («C»:=C) («f»:=f) («g»:=g)
      («W»:=W) («q»:=q) («piece»:=piece) («ordinary»:=ordinary) («reset»:=reset) («branch»:=branch) («positive»:=positive)
      («room»:=room) («shorten»:=shorten) («c»:=c) («j»:=j) («rest»:=rest) («base»:=base) («width»:=width)
      («age»:=age) («wFit»:=wFit) («qFit»:=qFit) («qh»:=qh) («template»:=template) («sitesPositive»:=sitesPositive) («rawWords»:=rawWords)
      («headerRows»:=headerRows) («paidRows»:=paidRows) («pool»:=pool) («raw»:=raw) («w»:=w) («K»:=K) («payloadBits»:=payloadBits)
      («fit»:=fit) («begin_»:=censusBase) («rom»:=rom) («peer»:=peerBank) («old»:=wingBank) («org»:=lookupBase) («homes»:=dateHomes)
      («other»:=other) («arity»:=arity) («groups»:=groups) («stride»:=stride) («oldTags»:=oldTags) («codec»:=codec) («lo»:=lo)
      («packWidth»:=packWidth) («all»:=all) («head»:=head) («short»:=short) («fence»:=fence) («count»:=count) («plan»:=plan)
      («primitive»:=primitiveImage_) («m»:=bookImage_) («original»:=original) captured ⟨packets.1,packets.2.1,packets.2.2.1⟩ sites)
  intro printed
  have actorWords := native_acquired_actor_words («F»:=F) («cp»:=cp) («P»:=P) («X»:=X) («G»:=G) («S»:=S) («k»:=k)
      («cut»:=cut) («tail»:=tail) («n»:=n) («h»:=h) («C»:=C) («f»:=f) («g»:=g)
      («W»:=W) («q»:=q) («piece»:=piece) («ordinary»:=ordinary) («reset»:=reset) («branch»:=branch) («positive»:=positive)
      («room»:=room) («shorten»:=shorten) («c»:=c) («j»:=j) («rest»:=rest) («headerRows»:=headerRows) («paidRows»:=paidRows)
      («w»:=w) («boardDegree»:=boardDegree) («board»:=board) («dateAge»:=dateAge) («dateDegree»:=dateDegree) («datePayload»:=datePayload) («ordinaryAt»:=ordinaryAt)
      («operandLanes»:=operandLanes) («primitiveLanes»:=primitiveLanes) («previousDate»:=previousDate) («priorAddress»:=priorAddress) («rosterBank»:=rosterBank) («datedFloor»:=datedFloor) («replayBase»:=replayBase)
      («matrixTable»:=matrixTable) («dateTag»:=dateTag) («dateRotation»:=dateRotation) («snapshots»:=snapshots) («roleBase»:=roleBase) («datedMem»:=datedMem) («dateInput»:=dateInput)
      («replayRoom»:=replayRoom) (date:=actual) (printed:=printed)
  have groupBits : groupsAt≤(dateSpec).printBits := by
    change groupsAt≤2+groupsAt*max (max 1 (Nat.clog 2 (q+1))) _
    exact (Nat.le_mul_of_pos_right _ (lt_of_lt_of_le (by decide : 0<1)
      ((le_max_left 1 (Nat.clog 2 (q+1))).trans (le_max_left _ _)))).trans (Nat.le_add_left ..)
  have wordWidth : (dateSpec).printBits≤w := by
    by_contra! large
    have order:=Nat.pow_le_pow_right (by decide : 0<2) large.le
    exact (not_le_of_gt printed) order
  let block : DescentColonies.Block k := ⟨0,Nat.two_pow_pos _⟩
  have sizes := ((dateSpec).prior censusBase).actorSize block
  have endAddr := (congrArg (fun bank : Bank => bank.base + bank.size)
    (MaskAllocation.Channels.occupied_at ((dateSpec).channels censusBase) block).symm).trans_le
    ((dateSpec).channels_before censusBase (finProdFinEquiv (block,(0:Fin 9))))
  have hostFits : H₀≤2^w := sizes.trans
    ((Nat.le_add_left ..).trans (endAddr.trans actual.wordRoom.le))
  exact ⟨hostFits,groupBits.trans wordWidth,actorWords⟩

/-- The true terminal source fixes the original three-table base, the replayed
home register, the primitive image, and the Book image from a single funded execution. -/
def WideEarnedPrimitiveSources : Prop := inputsAt_ lookupBase dateHomes bookImage_

/-- Every intended root address is the address selected by the actual scheduled machine. -/
def WidePrimitiveSources : Prop := inputs_

local notation "observedFmt" => ({fmt with binSize:=W}:Branch.PreflightFormat)
local notation "observedEqs" => Branch.preflight_caps (tail:=tail) X G S b observedFmt
local notation "observedHost" => (b).target.vertex.trans (Fin.castLEEmb (b).target.valid.host)
local notation "observedRasters" => Branch.presented (observedEqs).1 (observedEqs).2.1 ((pre).rasters censusBase peerBank wingBank)
local notation "observedPortRows" => fun rs => DescentTerminalLocalPortBook.Rasters.Inputs («p»:=p) (bw:=(pre).printBits) (argc:=Nat.clog 2 (q+1)) (b).target.placement observedHost S (b).target.valid (b).target.order rs observedRasters primitiveImage_
set_option maxHeartbeats 8500000
theorem wide_primitive_sources (source:inputs_) : published_ := by
  obtain ⟨paid,actors,budgetHeight,oldPeers,boot,romTop,full,space,rowCount,allRows,size,retained,headerLow,prior,late,ceiling,tableSide,bookWidth,pageReads,occ,oldCells,wideSeed,fitsSeed,topSeed,positiveGrain,below,before,lower,words,fits,geometry,top,apart,copyRoom,historyWords,exterior,history,window,homeSide,homeRead,rect,positiveWord,pack,leaves,roleCount,spare,smallPage,smallRows,smallCircuit,large,addressBits,date,remaining⟩:=source
  have returned := @PrimitiveDateRows.returned F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput oldPeers date
  have held := (Classical.choose_spec returned).1
  have observed:=Branch.scheduled_held_venue (X:=X) (g:=g) («p»:=p) (f:=f) (G:=G) (S:=S) (board:=board)
    (age:=dateAge) (degree:=dateDegree) (payload:=datePayload) (ordinary:=ordinaryAt)
    (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previous:=previousDate)
    (addr:=priorAddress) (oldRoster:=rosterBank) (floor:=datedFloor) (drift:=R) (op:=rot)
    («b»:=b) (radix:=ordinary.radix) («last»:=(@PrimitiveDateRows.lastDate F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput oldPeers date)) (oldK:=(@PrimitiveDateRows.previousBlocks F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput oldPeers date))
    (limit:=returned.choose) dateInput datedMem held
  have actorsAt:=returned.choose_spec.2
  have scalar := @Branch.reel_public_arity F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest base width age wFit qFit qh template sitesPositive rawWords headerRows paidRows pool raw w K fit censusBase rom peerBank wingBank org homes other arity groups stride oldTags codec lo packWidth head short primitiveImage_ paid actors boot romTop full space oldCells
  have raster := Branch.scheduled_raster_fields (tags:=tagCount) (X:=X) (G:=G) (S:=S) (baseGroups:=base) (radix:=ordinary.radix)
    (q:=q) («p»:=p) (g:=g) (drift:=R) (op:=rot) (headerRows:=headerRows) (paidRows:=paidRows)
    (board:=board) (age:=dateAge) (f:=f) (degree:=dateDegree) (payload:=datePayload) (ordinary:=ordinaryAt)
    (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previous:=previousDate) (addr:=priorAddress)
    (oldRoster:=rosterBank) (floor:=datedFloor) (j:=j) (r:=rest) (t:=s) (base:=replayBase)
    («compact»:=matrixTable) (tag:=dateTag) (rotation:=dateRotation) (A:=snapshots) (roleBase:=roleBase)
    (room:=replayRoom) («b»:=b) (u:=earlierPages) (m:=datedMem) («last»:=(@PrimitiveDateRows.lastDate F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput oldPeers date)) (oldK:=(@PrimitiveDateRows.previousBlocks F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput oldPeers date))
    (word:=(@PrimitiveDateRows.wordRoom F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput oldPeers date)) (positive:=(@PrimitiveDateRows.positiveWord F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput oldPeers date)) (alive:=(@PrimitiveDateRows.occupied F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput oldPeers date)) (prev:=(@PrimitiveDateRows.rotations F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput oldPeers date))
    (seed:=(@PrimitiveDateRows.matrix F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput oldPeers date)) (signedPitch:=(@PrimitiveDateRows.signedWidth F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput oldPeers date)) (rank:=(@PrimitiveDateRows.snapshotsFit F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput oldPeers date)) (roleEnd:=(@PrimitiveDateRows.roleTable F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput oldPeers date))
    (@PrimitiveDateRows.tailRoom F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput oldPeers date) observed actorsAt bookWidth scalar
  have peerEq : oldPeers=(b).target.terminalRoster (b).target.valid.host := date.roster
  have activeRaster : observedPortRows oldPeers := Eq.mpr (congrArg (fun peers => observedPortRows peers) peerEq) raster
  exact ⟨paid,actors,budgetHeight,oldPeers,boot,romTop,full,space,rowCount,allRows,size,retained,headerLow,prior,late,ceiling,tableSide,bookWidth,pageReads,occ,oldCells,wideSeed,fitsSeed,topSeed,positiveGrain,below,before,lower,words,fits,geometry,top,apart,copyRoom,historyWords,exterior,history,window,homeSide,homeRead,rect,positiveWord,pack,leaves,roleCount,spare,smallPage,smallRows,smallCircuit,large,addressBits,activeRaster,remaining⟩

/-- Discharge the observed roster from the original final-reset inputs with the
Book register itself fixed at the acquired memory. -/
theorem wide_earned_primitive_sources (source : inputsAt_ lookupBase dateHomes bookImage_) :
    publishedAt_ lookupBase dateHomes bookImage_ := by
  apply wide_primitive_sources (org:=lookupBase) (homes:=dateHomes) (m:=bookImage_)
  exact source


end
end Hierarchy.DescentSixParty.SeedNamed


-- These dependent theorem signatures are expensive in the library suggestion index.
-- Keep the exclusion local to this export so importing modules retain their search settings.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun prior =>
    ["native_acquired_actor_words", "native_acquired_population_word", "native_private_fields",
     "native_operand_receipts", "native_acquired_population_field", "native_acquired_operand_receipts",
     "native_acquired_sockets_receipts", "native_acquired_public_words", "wide_earned_from_registered",
     "wide_primitive_sources", "wide_earned_primitive_sources"] ++ prior

end OAI

import OAI.Hierarchy.DescentFinalArgumentCapacity
import OAI.Hierarchy.DescentNormalizedTerminalArgumentOrigin
import OAI.Hierarchy.DescentTerminalFrozenPointerWords
import OAI.Hierarchy.DescentNamedEarnedSiteBanks
import OAI.Hierarchy.DescentNamedWideFlightHeight

namespace OAI
/-! # Original calibrated site receipt after the full paid preflight and native socket reads -/
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

open DescentTerminalPointerDigits DescentTerminalPointerIssue DescentSIMDLookup

open DescentLocalPrivateNames in
private abbrev residentOperandNumber {tt ar : ℕ} (q₀ : ℕ) (r₀ : Recipe (Fin tt) (Fin ar))
    (hidden : r₀.Hidden ↪ ℕ) (u : r₀.Node) (j : Fin (r₀.arity u)) : ℕ :=
  (r₀.operand u j).elim (fun port => port.val+1) (fun name => q₀+(DescentTerminalChronologicalBooks.ordinal hidden name).val+1)

open DescentLocalPrivateNames in
private theorem residentOperandNumber_congr {tt ar : ℕ} (q₀ : ℕ) (r₀ : Recipe (Fin tt) (Fin ar))
    (earlierNames laterNames : r₀.Hidden ↪ ℕ) (same : ∀ a, DescentTerminalChronologicalBooks.ordinal earlierNames a = DescentTerminalChronologicalBooks.ordinal laterNames a)
    (u : r₀.Node) (j : Fin (r₀.arity u)) :
    residentOperandNumber q₀ r₀ earlierNames u j = residentOperandNumber q₀ r₀ laterNames u j := by
  exact congrArg (fun h => (r₀.operand u j).elim (fun a => a.val+1) h)
    (funext fun a => congrArg (fun slot : Fin (Fintype.card r₀.Hidden) => q₀+slot.val+1) (same a))

private theorem read_padded_bank {rows oldSlots newSlots count bits : ℕ}
    (ptr : Fin 4 → Fin oldSlots → Fin rows → Bank) (unused : Fin rows → Bank)
    (i : Fin count) (intoNew : count ≤ newSlots) (intoOld : count ≤ oldSlots)
    (col : Fin 4) (rack : Fin rows) (homeIndex : ℕ) (past present : Memory bits)
    (decodeWord : Computability.VPVNP.BurstRAM.Word bits → ℕ) (value : ℕ)
    (framed : present ((ptr col (i.castLE intoOld) rack).base+homeIndex) =
        past ((ptr col (i.castLE intoOld) rack).base+homeIndex))
    (read : decodeWord (past ((ptr col (i.castLE intoOld) rack).base+homeIndex)) = value) :
    decodeWord (present ((DescentTerminalOperandRepack.padded (K:=newSlots) ptr unused col (i.castLE intoNew) rack).base+homeIndex)) = value := by
  simp only [DescentTerminalOperandRepack.padded, Fin.val_castLE, dite_eq_left (i.isLt.trans_le intoOld)]
  exact (congrArg decodeWord framed).trans read

private theorem physical_arity_from_site {q₀ tags sites nodes args bits width groups blocks hosts value : ℕ}
    (machine : MaskedShelf blocks) (image : Memory width) (bank : Bank) (rack : Fin blocks)
    (placed : machine.channel (finProdFinEquiv (rack,(6 : Fin 8).succ)) = bank)
    (room_ : hosts ≤ (machine.channel (finProdFinEquiv (rack,(6 : Fin 8).succ))).size)
    (word : hosts ≤ 2^width) {i₁ i₂ : Fin hosts} (homeEq : i₁=i₂) (groupIndex : Fin groups)
    (slot : Fin nodes) (pop : ℕ) (widths : Fin 4 → ℕ)
    (arityAt : venueField (cellAt (measured (q:=q₀) (t:=tags) (H:=sites) (N:=nodes) (A:=args)
      (w:=bits) (groups:=groups) machine image i₂) (finProdFinEquiv (groupIndex,rack))) (nodeArity slot) = value) :
    (⟨pop,Nat.clog 2 (args+1),widths,some nodes⟩ : Widths).nodeDigit (Nat.clog 2 (args+1))
      slot.val groupIndex.val (image (bank.base+i₁.val)).val = value := by
  subst i₂
  exact (native_arity_digit (q:=q₀) (tags:=tags) (H:=sites) (N:=nodes) (A:=args) (p:=bits)
    machine image bank.base rack (congrArg Bank.base placed) room_ word i₁ groupIndex slot).symm.trans arityAt

private theorem site_layer_bounds (spec : DescentTerminalPreflightSpace.Spec) (origin : ℕ) :
    spec.cohortEnd origin ≤ spec.literalBase origin ∧ spec.literalBase origin ≤ spec.maskBase origin := by
  obtain ⟨a,b,c,d,e,f,g,h,i⟩ := spec.layers origin
  exact ⟨a.trans (b.trans (c.trans (d.trans (e.trans (f.trans g))))),h.trans i⟩

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
local notation "realPage" => MaskAllocation.shelf (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) («p»:=p)
  (groups:=groupsAt) ((dateSpec).channels censusBase) ((dateSpec).maskBase censusBase)
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
local notation "replayFree" => cellFront+DescentTerminalPublicIdentity.total K W q piece cellCodes rawWords
  (datePorts*2^(j+rest))
local notation "replayDst" => finalAt replayFree lo packWidth steps
local notation "slotNode" home:arg site:arg u:arg => (DescentTerminalChronologicalBooks.ordinal ((liveRanks home).atom site) u).castLE (nodeFit home site)
local notation "siteAddr" home:arg site:arg => finProdFinEquiv
  (((b).target.placement.pos ((homeOrd).node home site)).1,(b).target.placement.block ((homeOrd).node home site))
local notation "siteWord" home:arg site:arg key:arg =>
  venueField (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
    (cellAt (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
      (measured (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
        realPage primitiveImage_ home) (siteAddr home site)) key
variable (wideShort:((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).vertices*span q (DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))) (W*piece) (max 1 (max reset.bitsR (C*reset.bitsR)))) (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))) (S.epochPower^S.localTokenExponent) (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))) (W*piece)≤((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).pageBits)
local notation "datedRowsChecked" O:arg H:arg Q:arg test:arg mask:arg reelMask:arg nodeTest:arg => WideObservedSourcesWith (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (pool:=pool) (raw:=raw) (payloadBits:=payloadBits) (fit:=fit) (begin_:=censusBase) (rom:=rom)
      (peer:=peerBank) (old:=wingBank) (org:=O) (homes:=H) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=fence) (count:=count) (plan:=plan) (codec:=liveCodec) (arity:=max 8 (2^S.capGain)) (groups:=cap) (stride:=R) (oldTags:=dateColors) (short:=wideShort) (all:=all) (c:=c)
      (primitive:=primitiveImage_) (m:=Q) (original:=original) test mask reelMask nodeTest
local notation "paidPackets_" => WideMeasuredPackets (W:=W) (piece:=piece) (q:=q) (j:=j) (rest:=rest) (w:=w) (X:=X) (G:=G) (S:=S) (ordinary:=ordinary)
  (reset:=reset) (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (c:=c)
  (base:=base) (width:=width) (headerRows:=headerRows) (paidRows:=paidRows)
  (begin_:=censusBase) (peer:=peerBank) (old:=wingBank) (org:=lookupBase) (homes:=dateHomes)
  (primitive:=primitiveImage_) (m:=bookImage_)
local notation "ends" => datedRowsChecked lookupBase dateHomes bookImage_ (fun r=>r=actualRoster)
  (fun _:Prop=>True) (fun _:Prop=>True) (fun _:Prop=>True)

/-- The one-based role codes in the attained original primitive image. -/
def OriginalSiteRoleWords : Prop :=
  ∀(home : Fin H₀) (site : Fin (Fintype.card ((homeOrd).Nodes home))), ∀ (u : (liveRec home site).Node),siteWord home site (nodeRole (slotNode home site u))=((liveRec home site).tag u).val+1

/-- The per-node arities in the attained original primitive image. -/
abbrev OriginalSiteArityWords : Prop :=
  ∀(home : Fin H₀) (site : Fin (Fintype.card ((homeOrd).Nodes home))), ∀ (u : (liveRec home site).Node),siteWord home site (nodeArity (slotNode home site u))=(liveRec home site).arity u

private def emittedArgumentRows {tags publicPorts nodes arity : ℕ} (boundary : ℕ)
    (r : Recipe (Fin tags) (Fin publicPorts)) (position : r.Node → Fin nodes)
    (fits : ∀u, r.arity u ≤ arity) (names : r.Hidden ↪ ℕ)
    (field : Fin nodes → Fin arity → ℕ) : Prop :=
  ∀u, ∀a : Fin (r.arity u), field (position u) (a.castLE (fits u)) =
    (r.operand u a).elim (fun port => port.val+1)
      (fun h => boundary+(DescentTerminalChronologicalBooks.ordinal names h).val+1)

/-- The occupied operand cells in the attained original primitive image. -/
abbrev OriginalSiteArgumentWords : Prop :=
  ∀(i : Fin H₀) (z : Fin (Fintype.card ((homeOrd).Nodes i))),
    emittedArgumentRows q (liveRec i z) (fun u => slotNode i z u) (fun u => argFit i z u)
      ((liveRanks i).hidden z) (fun slot arg => siteWord i z (nodeArg slot arg))

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

/-- The three input fields read by the actual funded primitive and its named operand
printer, on every resident, in the original local and hidden ordinal order. -/
structure OriginalSiteWords : Prop where
  roles : originalWordField OriginalSiteRoleWords
  arities : originalWordField OriginalSiteArityWords
  «arguments» : originalWordField OriginalSiteArgumentWords

local notation "sourceWords" => OriginalSiteWords (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (c:=c) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh) (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows) (paidRows:=paidRows) (pool:=pool) (raw:=raw) (board:=board) (dateAge:=dateAge) (dateDegree:=dateDegree) (datePayload:=datePayload) (ordinaryAt:=ordinaryAt) (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previousDate:=previousDate) (priorAddress:=priorAddress) (rosterBank:=rosterBank) (datedFloor:=datedFloor) (replayBase:=replayBase) (matrixTable:=matrixTable) (dateTag:=dateTag) (dateRotation:=dateRotation) (snapshots:=snapshots) (roleBase:=roleBase) (datedMem:=datedMem) (replayRoom:=replayRoom)


/-- The expanded packet host bank is paid and published before the cohort prefix. -/
theorem earned_homes_after_replay : replayBase≤(dateHomes).base:=by
  have early := Branch.scheduled_base_le_early S k tail replayBase j rest s datePorts
  have slices : earlyFloor≤ sliceEnd:=by
    unfold Phase.stop DescentTerminalCompiledPrefix.AddressPlan.sliceStop DescentTerminalSliceShelf.fence
      DescentTerminalSliceShelf.stage DescentTerminalPointerDigits.Gather.rom DescentOperandStateBanks.guard
    simp only [Nat.add_assoc, Nat.le_add_right]
  obtain ⟨a₀,a₁,a₂,a₃,_⟩:=(dateCalendar).addresses sliceEnd 0
  have start : replayBase≤(dateCalendar).packetStart sliceEnd:=early.trans (slices.trans (a₀.trans a₁))
  exact start.trans (Nat.le_add_right ..)

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

/-- The recorded full branch bounds each original recipe's arity by the argument slots
of the physical terminal output, even after relabeling its scalar tags. -/
theorem final_argument_room (v : ((last).state c).graph.Site) (u : (observedRecipe v).Node) :
    (observedRecipe v).arity u≤(dateOut).argumentSlots :=by
  exact Branch.final_argument_capacity X G S b positive (Nat.le_max_left 1 (max reset.bitsR (C*reset.bitsR)))
    age branch v u


include base in
/-- All four packed input fields survive the original census and lookup scans
from their genuine terminal banks to the attained pointer reader. -/
theorem final_header_frame {rawPeers} (date:physicalRows rawPeers)
    (f₀:Fin 4) (j₀:Fin (dateOut).argumentSlots) (block:DescentColonies.Block k) (h₀:Fin H₀) :
    primitiveImage_ ((pointerBank f₀ j₀ block).base+h₀.val)=datedMem ((pointerBank f₀ j₀ block).base+h₀.val) := by
  have hit := native_earned_layout (base:=base) (dateTag:=dateTag) (replayRoom:=replayRoom) (date:=date)
  have held := hit.2.2.2.1
  have layoutProof :=Phase.scheduled_layout G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
    operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor date.lastDate
  have one:=Phase.scheduled_one G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
    operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor date.lastDate base date.signedWidth
  have end_:(dateOut).metadataEnd dateOrigin≤replayBase:=layoutProof.2.2.2.2.2.le.trans date.tailRoom
  have toCohort:replayBase≤(dateSpec).cohortEnd censusBase:=
    hit.2.2.2.2.1.trans (hit.2.2.2.2.2.1.trans hit.2.2.2.2.2.2)
  obtain ⟨a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈⟩:=(dateSpec).layers censusBase
  have word : replayBase<2^w := (toCohort.trans <| a₀.trans <| a₁.trans <| a₂.trans <| a₃.trans <|
    a₄.trans <| a₅.trans <| a₆.trans <| a₇.trans a₈).trans_lt date.wordRoom
  have read:=(dateOut).terminal_field_room dateOrigin (end_.trans_lt word)
    (f₀.castLE (by decide : 4≤7)) j₀ (block.cast blockCast)
  have rows:H₀≤(pointerBank f₀ j₀ block).size:=by
    have same := congrArg₂ Nat.mul layoutProof.2.1 one
    exact ((same.trans (Nat.mul_one _)).symm.le).trans read.2
  have orderProof :=(dateOut).terminal_order dateOrigin
  exact held _ ((Nat.add_lt_add_left (h₀.isLt.trans_le rows) _).trans_le
    (read.1.2.2.trans (orderProof.1.trans (orderProof.2.1.trans (orderProof.2.2.trans end_)))))

private theorem frozen_words_of_packets (acquired : paidPackets_) (i : Fin H₀) :
    primitiveImage_ (((dateSpec).frozenRoster censusBase).base+i.val)=
      ((Branch.frozenRosterCode X G S b positive base i : ℕ) : Computability.VPVNP.BurstRAM.Word w) :=
  (Fin.cast_val_eq_self _).symm.trans (congrArg (fun n : ℕ => (n : Computability.VPVNP.BurstRAM.Word w)) (acquired.2.2.2 i))

private theorem arity_row_capacity (spec : DescentTerminalPreflightSpace.Spec) (origin : ℕ)
    (rowIndex : Fin spec.scalar.blocks) : spec.scalar.shops ≤
        ((spec.channels origin).bank (finProdFinEquiv (rowIndex,(6 : Fin 8).succ))).size := by
  rw [MaskAllocation.Channels.primitive_at]
  exact spec.scalar.capacity (spec.primitive origin) (spec.population origin)
    (spec.scalar.subrow (spec.actors origin)) rowIndex 6 ((spec.prior origin).actorSize rowIndex)

private theorem shops_fit_mask (spec : DescentTerminalPreflightSpace.Spec) (origin : ℕ)
    {width : ℕ} (rowIndex : Fin spec.scalar.blocks) (room : spec.maskBase origin < 2^width) :
    spec.scalar.shops ≤ 2^width := by
  have toPrimitive : spec.scalar.shops ≤ spec.primitive origin :=
    ((spec.prior origin).actorSize rowIndex).trans ((Nat.le_add_left ..).trans ((spec.prior origin).actorEnd rowIndex))
  obtain ⟨_,p₁,p₂,p₃,p₄,p₅,p₆,p₇,p₈⟩ := spec.layers origin
  exact (toPrimitive.trans (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans (p₇.trans p₈)))))))).trans room.le

private theorem read_site_arity {rawPeers} (date : physicalRows rawPeers)
    (arities : originalWordField OriginalSiteArityWords) (home : Fin H₀)
    (site : Fin (Fintype.card ((homeOrd).Nodes home))) (t : (liveRec home site).Node) :
    let v := (homeOrd).node home site
    (operandWidths).nodeDigit (Nat.clog 2 (cap+1)) (rowPos v t).val ((observedGrid).pos v).1.val
      (primitiveImage_ (((cells).primitive ((observedGrid).block v) 6).base+((b).target.home v).val)).val =
        (observedRecipe v).arity t := by
  let v := (homeOrd).node home site
  let rack := (observedGrid).block v
  have atHome : (b).target.home v = home := (((homeOrd).nodes home).symm site).property
  exact physical_arity_from_site (q₀:=q) (tags:=allTags) (sites:=cap) (nodes:=nodeCap) (args:=cap) (bits:=p)
    realPage primitiveImage_ ((cells).primitive rack 6) rack (MaskAllocation.Channels.primitive_at cells rack 6)
    (arity_row_capacity dateSpec censusBase rack) (shops_fit_mask dateSpec censusBase rack date.wordRoom)
    atHome ((observedGrid).pos v).1 (rowPos v t) atomBits (fun _=>DescentOperandWidth.recordBits G S k tail R 3 p)
    (arities home site t)

set_option maxHeartbeats 2600000 in
/-- The actual fixed f7 printer reads the four earlier pointer fields, real arity,
wing panels, final matrix and frozen cohort code. Rectangular private names in its
lookup have the same first-use ordinal as the genuine local recipe. -/
theorem final_site_arguments {rawPeers} (date:physicalRows rawPeers) (acquired:paidPackets_)
    (matrixRead:primitiveImage_ matrixFloor=((DescentExterior.matrixCode
      (Branch.pinSpine X G S b positive base).matrix).val:Computability.VPVNP.BurstRAM.Word w))
    (previousFits:∀v,∀u,(observedRecipe v).arity u≤(dateOut).argumentSlots)
    (earlier:∀v,∀a:DescentLocalPrivateNames.Slot (observedRecipe v),∀f₀:Fin 4,
      (operandWidths).nodeDigit (DescentOperandWidth.recordBits G S k tail R 3 p)
        (rowPos v a.1).val ((observedGrid).pos v).1.val
        (datedMem ((pointerBank f₀ (a.2.castLE (previousFits v a.1)) ((observedGrid).block v)).base+
          ((b).target.home v).val)).val=(oldPtr v a).header f₀)
    (arities : originalWordField OriginalSiteArityWords) :
    originalWordField OriginalSiteArgumentWords := by
  obtain ⟨pointerWord,argumentWord,signedWord⟩:=final_operand_room (date:=date)
  intro home site u j₀
  let v:((last).state c).graph.Site:=(homeOrd).node home site
  let rack:DescentColonies.Block k:=(observedGrid).block v
  let grp:Fin groupsAt:=((observedGrid).pos v).1
  have atHome:(b).target.home v=home:=(((homeOrd).nodes home).symm site).property
  let recipe:=observedRecipe v
  let birth:=((trueLeaf).birth v)
  let nn:=rowCount v
  let aa:∀u,recipe.arity u≤cap:=fun u=>rowArity v u
  let aliases:=DescentTerminalPointerIssue.slot recipe birth nn (previousFits v)
  let opAt (a:DescentLocalPrivateNames.Slot recipe):DescentOperandStateBanks.Pointer:=oldPtr v a
  let wing:=DescentSharedCableNames.Stage.signedPanel observedGrid observedNative S (b).target.valid
    observedNames (DescentSharedCableNames.Stage.home observedGrid v)
  let observed:=issuedInputs recipe birth nn aa opAt wing
  let pages:=(dateSpec).pointerPages censusBase matrixFloor oldOperands wingBank
  let data:=pages.source (N:=nodeCap) (d:=(dateSpec).scalar.pointerBits) primitiveImage_ rack ((b).target.home v)
  have hostWord : H₀ ≤ 2^w := shops_fit_mask dateSpec censusBase rack date.wordRoom
  have ar (t:recipe.Node) : (operandWidths).nodeDigit (Nat.clog 2 (cap+1)) (rowPos v t).val grp.val
      (primitiveImage_ (((cells).primitive rack 6).base+((b).target.home v).val)).val=recipe.arity t:=by
    exact read_site_arity (date:=date) (arities:=arities) (home:=home) (site:=site) (t:=t)
  have field (a:DescentLocalPrivateNames.Slot recipe) (f₀:Fin 4) :
      (operandWidths).nodeDigit (DescentOperandWidth.recordBits G S k tail R 3 p) (rowPos v a.1).val grp.val
        (primitiveImage_ ((oldOperands f₀ (a.2.castLE (aa a.1)) rack).base+((b).target.home v).val)).val=
        (opAt a).header f₀:=by
    exact read_padded_bank pointerBank paidBank a.2 (aa a.1) (previousFits v a.1) f₀ rack ((b).target.home v).val
      datedMem primitiveImage_ (fun byte : Computability.VPVNP.BurstRAM.Word w =>
        (operandWidths).nodeDigit (DescentOperandWidth.recordBits G S k tail R 3 p) (rowPos v a.1).val grp.val byte.val)
      ((opAt a).header f₀) (final_header_frame (base:=base) (dateTag:=dateTag) (replayRoom:=replayRoom) (date:=date)
        (f₀:=f₀) (j₀:=a.2.castLE (previousFits v a.1)) (block:=rack) (h₀:=(b).target.home v)) (earlier v a f₀)
  have source:=Branch.fixed_pointer_issued_read (X:=X) (G:=G) (S:=S) («b»:=b) (q:=q)
    (drift:=R) (op:=rot) (headerRows:=headerRows) (paidRows:=paidRows) (origin:=censusBase)
    (romBase:=lookupBase) (w:=w) (paid:=paidBank) (actor:=actorBank) (roleBase:=roleBase)
    (peer:=peerBank) (signed:=wingBank) (rolePages:=(datePhase).banks earlyFloor)
    (matrix:=matrixFloor) (ptr:=pointerBank) (m:=dateEntry)
    v recipe birth nn aa opAt (native_acquired_population_word (base:=base) (age:=age) (dateTag:=dateTag) (replayRoom:=replayRoom) (date:=date) (precision:=date.paidPrecision) (acquired:=acquired) (v:=v))
    ar field signedWord (native_earned_wings (base:=base) (dateTag:=dateTag) (replayRoom:=replayRoom) (date:=date))
  have capacity:=DescentTerminalPointerDigits.input_bounds groupsAt nodeCap
    (S.groupWidth k tail 0+k) (k*S.length) (2^(8+S.capGain*S.length)) atomBits (Nat.clog 2 (cap+1))
    (DescentOperandWidth.recordBits G S k tail R 3 p) (DescentSignedCableCodec.width 3 (dateSpec).cap)
  have pins:=Branch.gathered_exterior_words (Nslots:=nodeCap) X G S b positive base pages primitiveImage_ rack
    (fun i=>by
      change primitiveImage_ (((dateSpec).frozenRoster censusBase).base+i.val)=
        ((Branch.frozenRosterCode X G S b positive base i : ℕ):Computability.VPVNP.BurstRAM.Word w)
      exact frozen_words_of_packets (acquired:=acquired) (i:=i))
    (by
      rw [(b).path.frozen_age]
      exact capacity.2.1) pointerWord ((b).target.home v) capacity.1 matrixRead
  have origin:=normalized_terminal_origin X G S ordinary reset branch positive room shorten c base v
    nn aa nn (previousFits v) observed (data mcol).val (data fcol).val pins.1 pins.2 rfl
    (issued_arity recipe birth nn aa opAt wing) (issued_pointer recipe birth nn aa opAt wing)
  let port:=(Branch.densePinEquiv X G S b positive base v).toEmbedding.trans Fin.valEmbedding
  let frozenAt (widthOfRoster : ℕ) : Prop :=
    DescentTerminalPointerIssue.Origin ((last).state c).graph v recipe birth nn aa aliases
      (Branch.leafOperands X G S b positive base v) port (reindexed observed
        (DescentExterior.terminalPin (S.groupWidth k tail 0+k) (S.groupWidth k tail S.length+k)
          widthOfRoster (data mcol).val (data fcol).val))
  have oldOrigin : frozenAt (b).path.frozen := origin
  have sameOrigin : frozenAt (k*S.length) := (congrArg frozenAt (b).path.frozen_age).mp oldOrigin
  have actual:=reached_fixed_argument (q:=q) observedGrid observedNative S (b).target.valid observedNames v
    (b).target.valid.coordinates port positive G.b (poolBatchCount (s*1) p)
    (by rw [(b).target.grain,Nat.mul_comm]) (fun _=>rfl) recipe (allCodes).store birth nn aa aliases observed
    (originalTier).1 (originalTier).2.1 operandWidths data grp.val terminalPin source
    sameOrigin rfl u j₀
  have small:=reference_fits (q:=q) observedGrid observedNative S (b).target.valid observedNames v port positive
    recipe (allCodes).store aliases ((Branch.final_slots X G S b positive v).trans qFit) (hiddenFit home site) u j₀
  have emitted:=Branch.scheduled_reference_digit (tags:=allTags) (X:=X) (G:=G) (S:=S) (baseGroups:=base)
    (q:=q) («p»:=p) (g:=g) (drift:=R) (op:=rot) (headerRows:=headerRows) (paidRows:=paidRows)
    (board:=board) (age:=dateAge) (f:=f) (degree:=dateDegree) (payload:=datePayload) (ordinary:=ordinaryAt)
    (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previous:=previousDate) (addr:=priorAddress)
    (oldRoster:=rosterBank) (floor:=datedFloor) (j:=j) (r:=rest) (t:=s) (base:=replayBase)
    («compact»:=matrixTable) (tag:=dateTag) (rotation:=dateRotation) (A:=snapshots) (roleBase:=roleBase)
    (room:=replayRoom) (m:=datedMem) («last»:=date.lastDate) (oldK:=date.previousBlocks) (word:=date.wordRoom)
    (signedPitch:=date.signedWidth) (roleEnd:=date.roleTable) date.tailRoom rack ((b).target.home v) grp
    (rowPos v u) (j₀.castLE (aa u)) hostWord argumentWord _ small actual
  let readHome (idx : Fin H₀) := venueField (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
    (cellAt (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
      (measured (q:=q) (t:=allTags) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
        realPage primitiveImage_ idx) (finProdFinEquiv (grp,rack))) (nodeArg (rowPos v u) (j₀.castLE (aa u)))
  let rect : recipe.UsedWord ↪ ℕ := (firstAlias recipe aliases).trans Fin.valEmbedding
  have serial (a : (liveRec home site).Hidden) :
      DescentTerminalChronologicalBooks.ordinal rect a = DescentTerminalChronologicalBooks.ordinal ((liveRanks home).hidden site) a :=
    rectangle_packed_ordinal recipe birth nn (previousFits v)
      (Branch.private_card_fit X G S b positive (Nat.le_max_left 1 (max reset.bitsR (C*reset.bitsR))) age branch v) a
  have atSlot := (congrArg readHome atHome).symm.trans emitted
  apply atSlot.trans
  exact residentOperandNumber_congr q (liveRec home site) rect ((liveRanks home).hidden site) serial u j₀


open DescentTerminalCombinedRole

local notation "readRoleNode" home:arg site:arg u:arg => DescentTerminalCombinedRole.fields (DescentTerminalCombinedRole.node (DescentTerminalCombinedRole.observed (n:=dateColors)
  (A:=max 8 (2^S.capGain)) (G:=cap) («p»:=p) («R»:=R) (N:=nodeCap) (M:=groupsAt) roleBanks
  primitiveImage_ ((finProdFinEquiv ((observedGrid).block ((homeOrd).node home site),home)).val:Computability.VPVNP.BurstRAM.Word w))
  (((observedGrid).pos ((homeOrd).node home site)).1) (slotNode home site u))

private theorem earned_role_widths {vertices groups q₀ tags sockets nodes lanes bits height word : ℕ}
    (small : groups ≤ vertices)
    (packed : vertices * DescentTerminalVertexFields.span q₀ tags sockets nodes sockets lanes ≤ bits)
    (page : 32 * bits ≤ height) (address : height / 2 ≤ word) :
    Nat.clog 2 (tags+1) * nodes * groups ≤ word ∧
    Nat.clog 2 (sockets+1) * nodes * groups ≤ word := by
  have limit : groups * DescentTerminalVertexFields.span q₀ tags sockets nodes sockets lanes ≤ word :=
    ((Nat.mul_le_mul_right _ small).trans packed).trans (by omega)
  have pay (n : ℕ) (fits : nodes*n ≤ DescentTerminalVertexFields.span q₀ tags sockets nodes sockets lanes) :
      n*nodes*groups ≤ word := by
    simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.mul_le_mul_left groups fits).trans limit
  constructor <;> apply pay <;> rw [DescentTerminalVertexFields.size] <;> omega

include wideShort in
/-- The joint sector span pays for each whole group of named role or arity outputs. -/
private theorem earned_role_output_room {scalarHeight : ℕ}
    (scalar:EarnedScalarArguments j s p q W allTags (dateSpec).pageBits (dateSpec).printBits scalarHeight w) :
    DescentTerminalCombinedRole.output dateColors (max 8 (2^S.capGain)) cap p R*nodeCap*groupsAt≤w ∧
    Nat.clog 2 (cap+1)*nodeCap*groupsAt≤w := by
  apply earned_role_widths (vertices := (pre).vertices) (bits := (dateSpec).pageBits) (height := scalarHeight)
    (q₀ := q) (lanes := p) (packed := wideShort) (page := scalar.page) (address := scalar.addressBits)
  change groupsAt ≤ groupsAt * 2^k
  exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)

private def siteRolePrintedAt {n A G : ℕ} {T Nodes : Type} (dictionary : Codec T n)
    (read : Nodes → DescentTerminalCombinedRole.Fields A G) (tag : Nodes → T)
    (slices : Nodes → List (List SliceCode)) : Prop :=
  ∀u, DescentTerminalCombinedRole.Printed dictionary (read u) (tag u) (slices u)

private theorem splitSiteWords {Hosts : Type} {Sites : Hosts → Type} {Nodes : (h : Hosts) → Sites h → Type}
    {P Q : (h : Hosts) → (z : Sites h) → Nodes h z → Prop}
    (both : ∀h z u, P h z u ∧ Q h z u) : (∀h z u, P h z u) ∧ (∀h z u, Q h z u) :=
  ⟨fun h z u => (both h z u).1, fun h z u => (both h z u).2⟩

include wideShort in
/-- The original two scans emit the role and flattened arity of each resident in
the exact native primitive returned by the paid replay. -/
theorem earned_site_role_scan_at_height {scalarHeight : ℕ} {rawPeers} (date:physicalRows rawPeers)
    (scalar:EarnedScalarArguments j s p q W allTags (dateSpec).pageBits (dateSpec).printBits scalarHeight w)
    (startRoom:replayBase<2^w) («copied»:Memory w)
    (mounted:datedMem=(originalRoleMount G rot S p R roleBase replayBase date.roleTable startRoom).phase.image «copied»)
    (printed : ∀(home : Fin H₀) (site : Fin (Fintype.card ((homeOrd).Nodes home))),
      siteRolePrintedAt liveCodec (fun u : (liveRec home site).Node => readRoleNode home site u)
        (fun u => ((trueLeaf).bit ((homeOrd).node home site)).tag u)
        (fun u => ((trueLeaf).shape ((homeOrd).node home site)).sliceFields u)) :
    originalWordField OriginalSiteRoleWords ∧ originalWordField OriginalSiteArityWords := by
  obtain ⟨roleCap,arityCap⟩:=earned_role_output_room (wideShort:=wideShort) (scalar:=scalar)
  have tables:=native_earned_role_tables (base:=base) (dateTag:=dateTag) (replayRoom:=replayRoom) (date:=date)
    (endAt:=date.roleTable) (wide:=startRoom) («copied»:=«copied») (mounted:=mounted) (input:=(datePhase).banks earlyFloor)
  apply splitSiteWords (Sites:=fun h : Fin H₀ => Fin (Fintype.card ((homeOrd).Nodes h)))
    (Nodes:=fun h z => (liveRec h z).Node)
  intro home site u
  let v:((last).state c).graph.Site:=(homeOrd).node home site
  have capU:(observedRecipe v).arity u≤cap:=rowArity v u
  have measured_:=Branch.scheduled_role_scan_fields (X:=X) (G:=G) (S:=S) (baseGroups:=base)
    (q:=q) («p»:=p) (hp:=positive) (g:=g) (drift:=R) (op:=rot) (headerRows:=headerRows) (paidRows:=paidRows)
    (board:=board) (age:=dateAge) (f:=f) (degree:=dateDegree) (payload:=datePayload) (ordinary:=ordinaryAt)
    (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previous:=previousDate) (addr:=priorAddress)
    (oldRoster:=rosterBank) (floor:=datedFloor) (j:=j) (r:=rest) (t:=s) (base:=replayBase)
    («compact»:=matrixTable) (tag:=dateTag) (rotation:=dateRotation) (A:=snapshots) (roleBase:=roleBase)
    (room:=replayRoom) (m:=datedMem) («last»:=date.lastDate) (oldK:=date.previousBlocks) (word:=date.wordRoom)
    (signedPitch:=date.signedWidth) (roleEnd:=date.roleTable) date.tailRoom liveCodec ((trueLeaf).shape v) u
    maskStart ((observedGrid).block v) home ((observedGrid).pos v).1 (slotNode home site u) roleCap arityCap
    (DescentPrimitivePalette.all_fit rot _) capU tables (printed home site u)
  exact measured_

include wideShort in
/-- Role and arity words at the reset height. -/
theorem earned_site_role_scan {rawPeers} (date:physicalRows rawPeers)
    (scalar:EarnedScalarArguments j s p q W allTags (dateSpec).pageBits (dateSpec).printBits h w)
    (startRoom:replayBase<2^w) («copied»:Memory w)
    (mounted:datedMem=(originalRoleMount G rot S p R roleBase replayBase date.roleTable startRoom).phase.image «copied»)
    (printed : ∀(home : Fin H₀) (site : Fin (Fintype.card ((homeOrd).Nodes home))),
      siteRolePrintedAt liveCodec (fun u : (liveRec home site).Node => readRoleNode home site u)
        (fun u => ((trueLeaf).bit ((homeOrd).node home site)).tag u)
        (fun u => ((trueLeaf).shape ((homeOrd).node home site)).sliceFields u)) :
    originalWordField OriginalSiteRoleWords ∧ originalWordField OriginalSiteArityWords :=
  earned_site_role_scan_at_height (base:=base) (dateTag:=dateTag) (replayRoom:=replayRoom)
    (wideShort:=wideShort) (date:=date) (scalar:=scalar) (startRoom:=startRoom)
    («copied»:=«copied») (mounted:=mounted) (printed:=printed)


set_option maxHeartbeats 3200000 in
/-- The earned site page on the original funded input. All five nontrivial fields of
every resident come from its native primitive image and the actual selected date.
The three sources below are the one-based role, true flat arity and named signed operand. -/
theorem original_earned_sites_at_height {scalarHeight : ℕ} (date:physicalRows actualRoster) (acquired:paidPackets_)
    (bins:W=NativeBranch.binLimit (k:=k) S)
    (scalar:EarnedScalarArguments j s p q W allTags (dateSpec).pageBits (dateSpec).printBits scalarHeight w)
    (rowsEq:(cfg).terminal.rows=paidRows) (localRows:(cfg).terminal.rows=K*W)
    (roomPool:(cfg).terminal.pool=K*W) (leaves:(cfg).terminal.leaves=(cfg).terminal.pool)
    (headerRowsFit:(cfg).terminal.pool≤headerRows)
    (headRoom:rom+DescentTerminalDenseHeaderBoot.extent q p≤replayFree)
    (early:replayFree≤replayBase) (afterFold:replayDst<replayBase) (startFence:maskStart≤fence)
    (area:AddressPlan.last cellV cfg cellInput cells maskStart<2^w)
    (dense:∀i<DescentTerminalDenseHeaderBoot.extent q p,datedMem (rom+i)=DescentTerminalDenseHeaderBoot.back w q p i)
    (roles : originalWordField OriginalSiteRoleWords)
    (arities : originalWordField OriginalSiteArityWords)
    («arguments» : originalWordField OriginalSiteArgumentWords) : ends:=by
  have lay := native_earned_layout (base:=base) (dateTag:=dateTag) (replayRoom:=replayRoom) (date:=date)
  have boot := lay.1
  have carried := lay.2.1
  have luts := lay.2.2.1
  have retained := lay.2.2.2.1
  have origin := lay.2.2.2.2.1
  have baseAfter := lay.2.2.2.2.2.1
  have cohort := lay.2.2.2.2.2.2
  have roster := native_earned_roster (base:=base) (dateTag:=dateTag) (replayRoom:=replayRoom) (date:=date)
  have rosterRoom := roster.1
  have peerWords := roster.2
  have limits := site_layer_bounds dateSpec censusBase
  have low:=early.trans (origin.trans (baseAfter.trans cohort))
  have upper := limits.1
  have romTop:=headRoom.trans (low.trans upper)
  have floor : replayFree≤ maskStart := low.trans (upper.trans limits.2)
  have preHomes : replayBase≤(dateHomes).base := earned_homes_after_replay (W:=W) (piece:=piece) (j:=j) (rest:=rest) X G S reset board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase snapshots
  have denseWords (i : ℕ) (bound : i < DescentTerminalDenseHeaderBoot.extent q p) :
      primitiveImage_ (rom+i) = DescentTerminalDenseHeaderBoot.back w q p i :=
    (retained _ ((Nat.add_lt_add_left bound rom).trans_le (headRoom.trans early))).trans (dense i bound)
  have priorRoof := afterFold.trans_le (origin.trans (baseAfter.trans cohort))
  have priorLuts := afterFold.trans_le origin
  have priorHomes := afterFold.trans_le preHomes
  have priorHeader := headRoom.trans low
  have finish := @wide_earned_site_pages_of_layout_at_height F _ cp P X G S k cut tail n h C f g W q piece
    ordinary reset branch positive room shorten c j rest base width age wFit qFit qh template sitesPositive
    rawWords headerRows paidRows pool raw w K payloadBits fit censusBase rom peerBank wingBank lookupBase dateHomes
    other (max 8 (2^S.capGain)) cap R dateColors liveCodec lo packWidth all head wideShort fence count plan
    primitiveImage_ bookImage_ original paidBank actorBank
  have socketAt := @native_acquired_sockets_receipts F _ cp P X G S k cut tail n h C f
    g W q piece ordinary reset branch positive room shorten c j rest base
    width age wFit qFit qh template sitesPositive rawWords headerRows paidRows pool raw w K
    fit rom other lo packWidth head boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes
    previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateTag dateRotation snapshots roleBase datedMem dateInput replayRoom
  subst W
  apply finish boot romTop floor rowsEq localRows roomPool carried priorRoof startFence priorLuts luts
    priorHomes leaves scalar rfl rosterRoom peerWords priorHeader denseWords headerRowsFit headRoom
  · intro home site
    exact @socketAt home site wideShort _ date acquired boot romTop floor area
      (roles home site) (arities home site) («arguments» home site)

theorem original_earned_sites_of_words_at_height {scalarHeight : ℕ} (date:physicalRows actualRoster) (acquired:paidPackets_)
    (bins:W=NativeBranch.binLimit (k:=k) S)
    (scalar:EarnedScalarArguments j s p q W allTags (dateSpec).pageBits (dateSpec).printBits scalarHeight w)
    (rowsEq:(cfg).terminal.rows=paidRows) (localRows:(cfg).terminal.rows=K*W)
    (roomPool:(cfg).terminal.pool=K*W) (leaves:(cfg).terminal.leaves=(cfg).terminal.pool)
    (headerRowsFit:(cfg).terminal.pool≤headerRows)
    (headRoom:rom+DescentTerminalDenseHeaderBoot.extent q p≤replayFree)
    (early:replayFree≤replayBase) (afterFold:replayDst<replayBase) (startFence:maskStart≤fence)
    (area:AddressPlan.last cellV cfg cellInput cells maskStart<2^w)
    (dense:∀i<DescentTerminalDenseHeaderBoot.extent q p,datedMem (rom+i)=DescentTerminalDenseHeaderBoot.back w q p i)
    (observed:sourceWords) : ends :=
  @original_earned_sites_at_height F _ cp P X G S k cut tail n h C f
    g W q piece ordinary reset branch positive room shorten c j rest base
    width age wFit qFit qh template sitesPositive rawWords headerRows paidRows pool raw w K
    payloadBits fit rom other lo packWidth all head fence count plan original boardDegree board
    dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateTag dateRotation
    snapshots roleBase datedMem dateInput replayRoom wideShort scalarHeight date acquired bins scalar rowsEq localRows roomPool leaves
    headerRowsFit headRoom early afterFold startFence area dense observed.roles observed.arities observed.«arguments»


/-- Earned sites when the scalar budget has the reset height. -/
theorem original_earned_sites (date:physicalRows actualRoster) (acquired:paidPackets_)
    (bins:W=NativeBranch.binLimit (k:=k) S)
    (scalar:EarnedScalarArguments j s p q W allTags (dateSpec).pageBits (dateSpec).printBits h w)
    (rowsEq:(cfg).terminal.rows=paidRows) (localRows:(cfg).terminal.rows=K*W)
    (roomPool:(cfg).terminal.pool=K*W) (leaves:(cfg).terminal.leaves=(cfg).terminal.pool)
    (headerRowsFit:(cfg).terminal.pool≤headerRows)
    (headRoom:rom+DescentTerminalDenseHeaderBoot.extent q p≤replayFree)
    (early:replayFree≤replayBase) (afterFold:replayDst<replayBase) (startFence:maskStart≤fence)
    (area:AddressPlan.last cellV cfg cellInput cells maskStart<2^w)
    (dense:∀i<DescentTerminalDenseHeaderBoot.extent q p,datedMem (rom+i)=DescentTerminalDenseHeaderBoot.back w q p i)
    (roles : originalWordField OriginalSiteRoleWords)
    (arities : originalWordField OriginalSiteArityWords)
    («arguments» : originalWordField OriginalSiteArgumentWords) : ends :=
  @original_earned_sites_at_height F _ cp P X G S k cut tail n h C f
    g W q piece ordinary reset branch positive room shorten c j rest base
    width age wFit qFit qh template sitesPositive rawWords headerRows paidRows pool raw w K
    payloadBits fit rom other lo packWidth all head fence count plan original boardDegree board
    dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateTag dateRotation
    snapshots roleBase datedMem dateInput replayRoom wideShort h date acquired bins scalar rowsEq localRows roomPool leaves
    headerRowsFit headRoom early afterFold startFence area dense roles arities «arguments»


theorem original_earned_sites_of_words (date:physicalRows actualRoster) (acquired:paidPackets_)
    (bins:W=NativeBranch.binLimit (k:=k) S)
    (scalar:EarnedScalarArguments j s p q W allTags (dateSpec).pageBits (dateSpec).printBits h w)
    (rowsEq:(cfg).terminal.rows=paidRows) (localRows:(cfg).terminal.rows=K*W)
    (roomPool:(cfg).terminal.pool=K*W) (leaves:(cfg).terminal.leaves=(cfg).terminal.pool)
    (headerRowsFit:(cfg).terminal.pool≤headerRows)
    (headRoom:rom+DescentTerminalDenseHeaderBoot.extent q p≤replayFree)
    (early:replayFree≤replayBase) (afterFold:replayDst<replayBase) (startFence:maskStart≤fence)
    (area:AddressPlan.last cellV cfg cellInput cells maskStart<2^w)
    (dense:∀i<DescentTerminalDenseHeaderBoot.extent q p,datedMem (rom+i)=DescentTerminalDenseHeaderBoot.back w q p i)
    (observed:sourceWords) : ends :=
  @original_earned_sites F _ cp P X G S k cut tail n h C f
    g W q piece ordinary reset branch positive room shorten c j rest base
    width age wFit qFit qh template sitesPositive rawWords headerRows paidRows pool raw w K
    payloadBits fit rom other lo packWidth all head fence count plan original boardDegree board
    dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateTag dateRotation
    snapshots roleBase datedMem dateInput replayRoom wideShort date acquired bins scalar rowsEq localRows roomPool leaves
    headerRowsFit headRoom early afterFold startFence area dense observed.roles observed.arities observed.«arguments»



end
end Hierarchy.DescentSixParty.SeedNamed

-- Keep suggestion indexing local to this file for the full acquired-site signatures.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun prior =>
  ["final_header_frame", "final_site_arguments", "earned_site_role_scan", "earned_site_role_scan_at_height",
    "original_earned_sites", "original_earned_sites_of_words", "original_earned_sites_at_height",
    "original_earned_sites_of_words_at_height"] ++ prior

end OAI

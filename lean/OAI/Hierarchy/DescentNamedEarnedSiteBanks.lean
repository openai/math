import OAI.Hierarchy.DescentOriginalRoleMount
import OAI.Hierarchy.DescentNamedFinalOperandRoom
import OAI.Hierarchy.DescentNamedWidePrimitiveSources
import OAI.Hierarchy.DescentNamedScheduledEarnedPages
import OAI.Hierarchy.DescentEarnedScalarArguments

namespace OAI
/-! # Native terminal Book and original roster inputs on the selected chronological heap -/
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
set_option maxHeartbeats 3000000
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
variable (headerRows paidRows : ℕ) {w : ℕ}
local notation "groupsAt" => S.groupCount S.length
local notation "fmt" => Branch.geometryFormat G S k g p tail q R rot headerRows paidRows
open DescentTerminalCompiledPrefix.AddressPlan DescentTerminalEmitter.Compact
open DescentTerminalLocalPortBook DescentTerminalSpanBook DescentTerminalBinPack
open DescentTerminalPreflightSpace ThreeFlat.RAM PhysicalProcedure
open DescentPackedEpochFold DescentExteriorMatrixUpdate DescentPackedSeed DescentSeedRoot
open ThreeFlat Routing Diagonal

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

/-- Every original dated cell below the replay roof survives at the scalar primitive
snapshot; all three lookup pages at the Book snapshot come from their native load. -/
theorem native_earned_layout {rawPeers} (date : physicalRows rawPeers) :
    (dateSpec).Before censusBase paidBank actorBank wingBank peerBank (lookupPage).total
      (lookupPage).modulo dateHomes (lookupPage).boundaries ∧
    (∀u,u<(dateSpec).weights censusBase→postEntry_ u=primitiveImage_ u) ∧
    (lookupPage).Reads bookImage_ ∧
    (∀u,u<replayBase→primitiveImage_ u=datedMem u) ∧
    replayBase≤lookupBase ∧ lookupBase≤censusBase ∧ censusBase≤(dateSpec).cohortEnd censusBase:=by
  have early := Branch.scheduled_base_le_early S k tail replayBase j rest s datePorts
  have slices : earlyFloor≤ sliceEnd:=by
    unfold Phase.stop DescentTerminalCompiledPrefix.AddressPlan.sliceStop DescentTerminalSliceShelf.fence
      DescentTerminalSliceShelf.stage DescentTerminalPointerDigits.Gather.rom DescentOperandStateBanks.guard
    simp only [Nat.add_assoc, Nat.le_add_right]
  obtain ⟨a₀,a₁,a₂,a₃,_⟩:=(dateCalendar).addresses sliceEnd 0
  have rootLower : replayBase≤lookupBase:=early.trans (slices.trans (a₀.trans (a₁.trans a₂)))
  have pagesLower:lookupBase≤censusBase:=Nat.le_add_right ..
  have weights:replayBase≤(dateSpec).weights censusBase:=rootLower.trans (pagesLower.trans
    (((dateSpec).cohort_le censusBase).trans (((dateSpec).layers censusBase).1.trans ((dateSpec).layers censusBase).2.1)))
  have dates:=Branch.scheduled_earned_pages X G S base ordinary.radix g p q R rot headerRows paidRows
    board dateAge f dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress
    rosterBank datedFloor j rest s replayBase matrixTable dateTag dateRotation snapshots roleBase replayRoom
    date.lastDate date.previousBlocks date.wordRoom date.positiveWord date.occupied (date.tailRoom.trans early)
    date.signedWidth date.snapshotsFit date.roleTable datedMem
  have out:=Branch.scheduled_original_preflight X G S base ordinary.radix g p q R rot headerRows paidRows
    board dateAge f dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress
    rosterBank datedFloor j rest s replayBase matrixTable dateTag dateRotation snapshots roleBase replayRoom
    date.lastDate date.previousBlocks date.wordRoom date.positiveWord date.occupied date.rotations date.matrix
    (date.tailRoom.trans early) date.signedWidth date.snapshotsFit date.roleTable datedMem
  refine ⟨dates.1,dates.2.1,dates.2.2,?_,rootLower,pagesLower,(dateSpec).cohort_le censusBase⟩
  intro u below
  exact (dates.2.1 u (below.trans_le weights)).symm.trans (out.1.2.2.1 u (.inl below))

private def rosterSnapshot {hosts degree bits : ℕ} (bank : ProtocolRAM.Bank) (mem : Memory bits)
    (roster : Fin hosts → Fin degree → Option (Fin hosts)) : Prop :=
  hosts * degree ≤ bank.size ∧ ∀ (h : Fin hosts) (j : Fin degree),
    mem (bank.base + (h.val * degree + j.val)) = (DescentPackedColony.target (roster h j) : Computability.VPVNP.BurstRAM.Word bits)

private def wingSnapshot {blocks sockets degree hosts lanes bits : ℕ}
    (wing : Fin blocks → Fin (2*sockets) → ProtocolRAM.Bank)
    (signed : Fin blocks → Fin (2*sockets) → Fin hosts → Fin lanes → Option (DescentSharedCableNames.Stage.Live degree sockets))
    (mem : Memory bits) : Prop :=
  ∀ x t, DescentPackedColony.Reads (wing x t) (fun h g => DescentSignedCableCodec.encode (signed x t h g)) lanes mem

private theorem earnedDateOutputBound {rawPeers} (date : physicalRows rawPeers) : (dateOut).fullEnd dateOrigin ≤ replayBase := by
  have last_date := @PrimitiveDateRows.lastDate F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput rawPeers date
  have tail_room := @PrimitiveDateRows.tailRoom F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput rawPeers date
  have layout := Phase.scheduled_layout G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
    operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor last_date
  have metadata : (dateOut).metadataEnd dateOrigin ≤ replayBase := layout.2.2.2.2.2.le.trans tail_room
  have ordered := (dateOut).terminal_order dateOrigin
  exact ordered.2.1.trans (ordered.2.2.trans metadata)

include base dateTag replayRoom in
private theorem earnedReplayWordRoom {rawPeers} (date : physicalRows rawPeers) : replayBase < 2^w := by
  have hit := native_earned_layout (base:=base) (dateTag:=dateTag) (replayRoom:=replayRoom) (date:=date)
  have toCohort:replayBase≤(dateSpec).cohortEnd censusBase:=
    hit.2.2.2.2.1.trans (hit.2.2.2.2.2.1.trans hit.2.2.2.2.2.2)
  obtain ⟨a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈⟩:=(dateSpec).layers censusBase
  exact (toCohort.trans <| a₀.trans <| a₁.trans <| a₂.trans <| a₃.trans <|
    a₄.trans <| a₅.trans <| a₆.trans <| a₇.trans a₈).trans_lt date.wordRoom

include base in
/-- The final reached venue determines the complete native sorted peer word,
including the sentinel in every unoccupied peer entry. -/
theorem native_earned_roster {rawPeers} (date : physicalRows rawPeers) :
    rosterSnapshot (hosts:=S.hostSize S.length) (degree:=(dateSpec).degree) (bits:=w) peerBank primitiveImage_
      (Branch.fixedRoster (H:=H₀) (d:=(b).target.placement.degree) (e:=(dateSpec).degree) (originalTier).1 actualRoster):=by
  have dated (a : ℕ) (ha : a < replayBase) : primitiveImage_ a = datedMem a :=
    (native_earned_layout (base:=base) (dateTag:=dateTag) (replayRoom:=replayRoom) (date:=date)).2.2.2.1 a ha
  have returned := @PrimitiveDateRows.returned F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput rawPeers date
  have held := (Classical.choose_spec returned).1
  have observed:=Branch.scheduled_held_venue (X:=X) (g:=g) («p»:=p) (f:=f) (G:=G) (S:=S) (board:=board)
    (age:=dateAge) (degree:=dateDegree) (payload:=datePayload) (ordinary:=ordinaryAt)
    (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previous:=previousDate)
    (addr:=priorAddress) (oldRoster:=rosterBank) (floor:=datedFloor) (drift:=R) (op:=rot)
    («b»:=b) (radix:=ordinary.radix) («last»:=(@PrimitiveDateRows.lastDate F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput rawPeers date)) (oldK:=(@PrimitiveDateRows.previousBlocks F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput rawPeers date))
    (limit:=returned.choose) dateInput datedMem held
  have eqn: (b).target.placement.degree=(dateSpec).degree:=(originalTier).1
  have peerEq := ((dateOut).terminal_venue_banks dateOrigin earlierPages 0 0).2.2.2
  have room₀ : H₀*(b).target.placement.degree≤(peerBank).size:=by
    rw [← peerEq]
    simpa only [(b).target.branch, Dated.Operands.ports] using observed.1.rosterRoom
  have upper := earnedDateOutputBound (date:=date)
  have top : (peerBank).base + (peerBank).size ≤ replayBase := ((dateOut).terminal_peer_room dateOrigin).1.trans upper
  refine ⟨(congrArg (fun degree => (S.hostSize S.length) * degree) eqn).symm.le.trans room₀,?_⟩
  intro h j
  let j₀:=j.cast eqn.symm
  have chosen : h.val*(b).target.placement.degree+j₀.val<H₀*(b).target.placement.degree:=by
    simpa only [finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm] using (finProdFinEquiv (h,j₀)).isLt
  have lookup:=(b).target.terminal_roster_words (b).target.valid.host _ observed h j₀
  have native:=dated _ ((Nat.add_lt_add_left (chosen.trans_le room₀) _).trans_le top)
  have address : (peerBank).base+(h.val*(b).target.placement.degree+j₀.val)=
      (peerBank).base+(h.val*(dateSpec).degree+j.val):=by
    change (peerBank).base+(h.val*(b).target.placement.degree+j.val)=_
    rw [eqn]
  exact (congrArg primitiveImage_ address.symm).trans (native.trans lookup)

open private wing_address from OAI.Hierarchy.DescentNamedScheduledRasters

include base in
/-- Each signed wing, including a vacant port or a padded host, survives unchanged
from the held final venue into its original terminal raster. -/
theorem native_earned_wings {rawPeers} (date : physicalRows rawPeers) :
    wingSnapshot (blocks:=2^k) (sockets:=(b).target.placement.cap) (degree:=(b).target.placement.degree)
      (hosts:=S.hostSize S.length) (lanes:=S.groupCount S.length) (bits:=w)
      (Branch.presented (d:=(b).target.placement.degree) (d':=(dateSpec).degree) (k:=2^k)
        («c»:=(b).target.placement.cap) (c':=(dateSpec).cap) (originalTier).1 (originalTier).2.1
        ((dateSpec).rasters censusBase peerBank wingBank)).wing
      (Prepare.signed (b).target.placement ((b).target.order.trans Fin.valEmbedding) S (b).target.valid
        (Function.Embedding.refl _) ((b).target.vertex.trans (Fin.castLEEmb (b).target.valid.host))) primitiveImage_:=by
  have dated (a : ℕ) (ha : a < replayBase) : primitiveImage_ a = datedMem a :=
    (native_earned_layout (base:=base) (dateTag:=dateTag) (replayRoom:=replayRoom) (date:=date)).2.2.2.1 a ha
  have returned := @PrimitiveDateRows.returned F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput rawPeers date
  have held := (Classical.choose_spec returned).1
  have observed:=Branch.scheduled_held_venue (X:=X) (g:=g) («p»:=p) (f:=f) (G:=G) (S:=S) (board:=board)
    (age:=dateAge) (degree:=dateDegree) (payload:=datePayload) (ordinary:=ordinaryAt)
    (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previous:=previousDate)
    (addr:=priorAddress) (oldRoster:=rosterBank) (floor:=datedFloor) (drift:=R) (op:=rot)
    («b»:=b) (radix:=ordinary.radix) («last»:=(@PrimitiveDateRows.lastDate F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput rawPeers date)) (oldK:=(@PrimitiveDateRows.previousBlocks F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput rawPeers date))
    (limit:=returned.choose) dateInput datedMem held
  have placed := earnedDateOutputBound (date:=date)
  have ceiling := earnedReplayWordRoom (base:=base) (dateTag:=dateTag) (replayRoom:=replayRoom) (date:=date)
  have shape := PhysicalReset.scheduled_terminal_shape G S board k tail dateAge p f g R
    dateDegree datePayload ordinaryAt rot s Z operandLanes primitiveLanes previousDate priorAddress
    rosterBank datedFloor (@PrimitiveDateRows.lastDate F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput rawPeers date) (@PrimitiveDateRows.previousBlocks F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten c j rest headerRows paidRows w boardDegree board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor replayBase matrixTable dateRotation snapshots roleBase datedMem dateInput rawPeers date)
  have kind:=shape.1
  have shops:=shape.2.1
  have grouped:=shape.2.2.1
  have capacity:=shape.2.2.2.1
  have lanes:=shape.2.2.2.2
  have capMatch:(dateVenue).cap=(b).target.placement.cap:=capacity.trans (originalTier).2.1.symm
  intro block t row_
  have address:=wing_address (d:=(b).target.placement.degree) (d':=(dateSpec).degree) («c»:=(b).target.placement.cap) (c':=(dateSpec).cap) (blockCount:=2^k) (originalTier).1 (originalTier).2.1 peerBank ((dateSpec).channels censusBase)
    ((dateOut).terminalWing dateOrigin) block t
  have transported := congrArg (fun page : ProtocolRAM.Bank => primitiveImage_ (page.base+(row H₀ groupsAt groupsAt row_).val)) address
  have widths:=(dateOut).terminal_wing_room dateOrigin (placed.trans_lt ceiling)
    (block.cast (congrArg (2^·) kind).symm) (t.cast (congrArg (2*·) capMatch).symm)
  have span : H₀*chunks groupsAt groupsAt≤((dateOut).terminalWing dateOrigin block.val t.val).size:=by
    have same : (dateVenue).hosts * chunks (dateVenue).groups (dateVenue).lanes =
        (S.hostSize S.length) * chunks groupsAt groupsAt :=
      congrArg₂ Nat.mul shops (congrArg₂ DescentSIMDLookup.chunks grouped lanes)
    exact same.symm.le.trans widths.2
  have low : _<replayBase := (Nat.add_lt_add_left ((row H₀ groupsAt groupsAt row_).isLt.trans_le span) _).trans_le
    (widths.1.trans placed)
  have cable := observed.2.2.2.1 block t row_
  have wingEq := ((dateOut).terminal_venue_banks dateOrigin earlierPages block.val t.val).2.2.1
  have transfer := congrArg (fun page : ProtocolRAM.Bank => datedMem (page.base+(row H₀ groupsAt groupsAt row_).val)) wingEq
  exact transported.trans ((dated _ low).trans (transfer.symm.trans cable))




/-- Widths of all packed fields consumed by the final normalized argument reader. -/
theorem final_operand_room {rawPeers} (date : physicalRows rawPeers) :
    (dateSpec).scalar.pointerBits≤w ∧
    (Nat.clog 2 (q+cap+1)*(nodeCap*cap))*groupsAt≤w ∧
    DescentSignedCableCodec.width (b).target.placement.degree (b).target.placement.cap*groupsAt≤w:=by
  have fits := Branch.final_operand_widths X G S k g p tail q R rot headerRows paidRows censusBase w date.wordRoom
  have signed := congrArg₂ DescentSignedCableCodec.width (originalTier).1 (originalTier).2.1
  exact ⟨fits.1, fits.2.1, (congrArg (fun n => n*groupsAt≤w) signed).mpr fits.2.2⟩



local notation "dict" => DescentPrimitivePalette.codec (G:=G) («s»:=S.firstWidth G.b p) («Z»:=S.grainAt G.b p 0) rot
local notation "wordCounts" => originalRoleBits G rot S p R
local notation "roleColors" => DescentPrimitivePalette.colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) rot
local notation "roleBound" => max 8 (2^S.capGain)

include base in
/-- Published words of every native role/arity table are unchanged by the early reel, sorted
slices, original census and preflight preceding the first requested primitive. -/
theorem native_earned_role_tables {rawPeers} (date:physicalRows rawPeers)
    (endAt:roleBase+DescentTerminalRoleTables.count wordCounts≤replayBase)
    (wide:replayBase<2^w) («copied»:Memory w)
    (mounted:datedMem=(originalRoleMount G rot S p R roleBase replayBase endAt wide).phase.image «copied»)
    (input:Fin 6→ProtocolRAM.Bank) :
    DescentTerminalCombinedRole.Static (A:=roleBound) (G:=cap) («p»:=p) («R»:=R) (N:=nodeCap) (M:=groupsAt)
      dict (DescentTerminalRoleTables.role wordCounts input roleBase) primitiveImage_ ∧
    DescentTerminalCombinedRole.CountStatic (n:=roleColors) (A:=roleBound) (G:=cap) («p»:=p) («R»:=R) (N:=nodeCap)
      (M:=groupsAt) cap (DescentTerminalRoleTables.arity wordCounts input roleBase) primitiveImage_ :=by
  apply original_role_after_replay G rot S p R roleBase replayBase endAt wide input «copied»
  intro a beforeEnd
  exact ((native_earned_layout (base:=base) (dateTag:=dateTag) (replayRoom:=replayRoom) (date:=date)).2.2.2.1 a beforeEnd).trans (congrFun mounted a)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

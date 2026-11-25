import OAI.Hierarchy.DescentRegisterVenueFormat
import OAI.Hierarchy.DescentNamedWidePrimitiveSources
import OAI.Hierarchy.DescentIssuedLastReset
import OAI.Hierarchy.DescentRegisteredPrefixRooms
import OAI.Hierarchy.DescentFinalResetActorRegister
import OAI.Hierarchy.DescentLowCountBook
import OAI.Hierarchy.DescentResetTerminalCenters
import OAI.Hierarchy.DescentResetVenueSourceLower

namespace OAI
/-! # Primitive raster registers on the last issued finite-cut instruction -/
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
local notation "s" => S.firstWidth G.b p
local notation "Z" => S.grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
open Chronology Chronology.RegisterTimeline DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentExteriorReplay DescentTerminalFixedSlices DescentSeedRoot DescentActorRaster DescentColonies
open DescentTerminalRoleTables DescentTerminalCombinedRole DescentPackedColony
variable {j rest w boardDegree : ℕ} (age : 0<S.height)
  (board:NonlinearExpanders.Graph n boardDegree) (dateDegree datePayload header : ℕ)
  (ordinaryAt : ℕ→Dated.Ordinary) (profile : ℕ→ℕ) (first : Position) (mem : Memory w)
  (headerRows paidRows replayBase matrixTable roleBase : ℕ) (dateRotation : ℕ→ℕ) (snapshots : Snapshots k)
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "ticket" => issuedFinalReset X G S ordinary reset branch positive room shorten c age
variable (seats : ℕ→ℕ)
local notation "menu" => (⟨board,rot,g,tail,p,f,R,dateDegree,datePayload,seats,ordinaryAt,profile,header⟩:Menu n boardDegree)
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu first
local notation "codes" => instruction (w:=w) traces menu first
local notation "steps" => RegisterTimeline.issued (w:=w) traces menu
local notation "family" => RunTrace.machine traces (fun i _=>codes i)
local notation "dateAge" => S.length-1
local notation "old" => cursor dateAge
local notation "previousDate" => (old).ports.venue
local notation "operandLanes" => (old).ports.operandLanes
local notation "primitiveLanes" => (old).ports.roleLanes
local notation "priorAddress" => (old).ports.io.wire
local notation "rosterBank" => (old).ports.io.roster
local notation "datedFloor" => (old).ports.priorStart k (old).floor
local notation "datedMem" => DateCode.history family mem S.length
local notation "dateSpec" => SeedNamed.Branch.preflightSpec X G S k g p tail (SeedNamed.Branch.geometryFormat G S k g p tail q R rot headerRows paidRows)
local notation "datePorts" => Fintype.card (Port P X.width)
local notation "datePhase" => Phase.scheduled G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
  operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
local notation "dateOut" => (datePhase).output
local notation "dateOrigin" => (datePhase).dateBase
local notation "dateMachine" => PhysicalReset.scheduled G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
  s Z operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
local notation "dateCalendar" => SeedNamed.Branch.replayCalendar X S k tail j rest snapshots
local notation "earlyFloor" => DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail replayBase j rest s datePorts
local notation "sliceEnd" => (datePhase).stop earlyFloor
local notation "lookupBase" => (dateCalendar).packetEnd sliceEnd
local notation "lookupPage" => (dateSpec).scanPages lookupBase q
local notation "censusBase" => (lookupPage).stop
local notation "dateVenue" => (dateOut).venue.next
local notation "dateHardware" => (dateOut).receiver
local notation "dateShops" => (dateSpec).scalar.shops
local notation "dateBlocks" => (dateSpec).scalar.blocks
local notation "actorBank" => fun x:Fin dateBlocks=>(dateOut).terminalActor dateOrigin x.val
local notation "dateColors" => DescentPrimitivePalette.colors G s Z rot
local notation "roleBankBits" => fun field:Fin 6=>DescentTerminalCombinedRole.width dateColors (max 8 (2^S.capGain))
  (NativeBranch.privateSlotCapacity G S R) p R field*(S.epochPower^S.localTokenExponent)*(dateSpec).groups
local notation:max "input_" sp:arg => DatePorts.resetInputs G S board k tail dateAge p f g R dateDegree datePayload
  ordinaryAt rot s Z (old).ports (old).floor w sp
local notation:max "rowsAt" sp:arg m:arg => PrimitiveDateRows («q»:=q) («j»:=j) («rest»:=rest) («W»:=W) («piece»:=piece) («X»:=X) («G»:=G) («S»:=S) («ordinary»:=ordinary) («reset»:=reset) («branch»:=branch) («positive»:=positive)
    («room»:=room) («shorten»:=shorten) («c»:=c) («board»:=board) («dateAge»:=dateAge) («dateDegree»:=dateDegree)
    («datePayload»:=datePayload) («ordinaryAt»:=ordinaryAt) («operandLanes»:=operandLanes) («primitiveLanes»:=primitiveLanes)
    («previousDate»:=previousDate) («priorAddress»:=priorAddress) («rosterBank»:=rosterBank) («datedFloor»:=datedFloor)
    («replayBase»:=replayBase) («matrixTable»:=matrixTable) («dateRotation»:=dateRotation)
    («snapshots»:=snapshots) («roleBase»:=roleBase) («dateInput»:=input_ sp) («datedMem»:=m)
    («headerRows»:=headerRows) («paidRows»:=paidRows)
local notation:max "physicalRows" sp:arg => rowsAt sp datedMem
variable (fixed : ∀i (a z : RunTrace.Events traces i) x y,
      steps i a (cursor i) x → steps i z (cursor i) y → x=y)
    (origin : first.ports.held (b).origin.source first.floor mem) (limit : ℕ) (valid : Prop)
    (runs : ∀i (e : (traces c).path.Event i),advances traces menu first c mem limit valid i e)
    (live : (b).path.selections.length<limit ∨ valid)
    (startRooms : Rooms G S menu k w 0 first)
    (installed : ∀i (e : RunTrace.Events traces i),Rooms G S menu k w i (cursor i)→
       ∃mv:Move w,steps i e (cursor i) mv ∧ mv.next.floor<2^w ∧
         (e.2.isReset=true→8*(menu).receiverWidth G S k i (cursor i).ports≤datePayload))

set_option hygiene true
attribute [local irreducible] SeedNamed.issued normalizedPackedChart

section LastResetRows
attribute [local irreducible] DatePorts.held Path.Event.actorPlanes issuedFinalReset

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 8192 in
include fixed origin runs live startRooms installed in
/-- The terminal preflight's native data register, on the shared finite-cut
execution of the issued ballot and its registered preceding venue. -/
theorem issued_primitive_date_rows
    (actors : (ticket).event.actorPlanes actorBank (DateCode.history codes mem S.length))
    (format : VenueFormat S menu k dateAge old) (maskRoom : (dateSpec).maskBase censusBase<2^w)
    (word : 0<w) (shops : 0<dateShops) (rotations : ∀i<S.length,dateRotation i<replayBase)
    (matrix : matrixTable+32*DescentExteriorShelf.span j rest s datePorts≤replayBase)
    (signed : (dateVenue).signedLanes=S.groupCount S.length)
    (snaps : ∀t<S.length,∀bank,snapshots.compact t=some bank→bank.Fits w replayBase)
    (roles : roleBase+DescentTerminalRoleTables.count roleBankBits≤replayBase)
    (terminal : (cursor S.length).floor≤replayBase) :
    ∃space,(physicalRows space) ((b).target.terminalRoster (b).target.valid.host) :=by
  have address:=rooms_on_event traces menu first fixed startRooms installed c dateAge (ticket).event
  have step_ := installed dateAge ⟨c,(ticket).event⟩ address
  have bootAt : first.ports.held (traces c).first first.floor mem := by
    dsimp only [traceAt]
    exact origin
  have liveAt : (traces c).path.selections.length < limit ∨ valid := by
    dsimp only [traceAt]
    exact live
  have present : ∃ mv, steps dateAge ⟨c,(ticket).event⟩ old mv :=
    ⟨step_.choose,step_.choose_spec.1⟩
  have nativeActors : (ticket).event.actorPlanes
      (fun x : DescentColonies.Block k => (dateMachine).successor.terminalActor
        ((dateMachine).rebased ((dateMachine).stageStart datedFloor)) x.val) (DateCode.history codes mem S.length) := actors
  have lastData := last_reset_register («p»:=W*piece) traces menu first c mem limit valid fixed
    bootAt runs ticket liveAt present nativeActors
  let space := lastData.choose_spec.choose
  have data := lastData.choose_spec.choose_spec
  have end_ : (dateMachine).fullEnd datedFloor≤replayBase :=
    (congrArg Position.floor data.2.1).ge.trans terminal
  refine ⟨space,rfl,(ticket).succ_age,format.width,format.paid,maskRoom,word,shops,rotations,matrix,signed,snaps,roles,end_,?_⟩
  exact ⟨(dateMachine).fullEnd datedFloor,data.2.2.1,data.2.2.2⟩

end LastResetRows

theorem initial_before_last : first.floor≤(old).floor:=by
  rw [position_floor steps first dateAge]
  exact DescentDatedAddressBook.floor_mono first.floor (span steps first) (Nat.zero_le dateAge)

/-- Preserve the issued raster register when the public history counter copies
its selected scalar words into the earlier count array. -/
theorem issued_primitive_date_rows_after_capture
    (capture count:ℕ) (source:ℕ→ℕ) (below:capture+count≤(old).floor)
    {space} {raw} (earlier:(physicalRows space) raw) :
    (rowsAt space (DescentLowCountBook.output capture source datedMem count)) raw :=by
  let m:=DescentLowCountBook.output capture source datedMem count
  let low:=capture+count
  let a:=dateMachine
  let out:=a.successor
  let u:=input_ space
  let loc:=a.rebased (a.stageStart datedFloor)
  have high : low≤loc:=by
    have shift:=((old).ports.resetPad k).cuts (old).floor
    have roots:=a.occupied (a.stageStart datedFloor)
    have beforePresence:=below.trans (shift.1.trans shift.2)
    have atEntry : low≤datedFloor:=beforePresence.trans (((old).ports.presence k).lower _)
    exact ((atEntry.trans (a.ingress.after datedFloor)).trans roots.1).trans roots.2.1
  have fixed (j:ℕ) (kept:low≤j) : m j=datedMem j:=DescentLowCountBook.frame capture source datedMem count j (.inr kept)
  obtain ⟨limit,⟨wide,register,num⟩,alive⟩:=earlier.returned
  have centers:=out.terminal_centers_above loc
  refine ⟨earlier.roster,earlier.lastDate,earlier.previousBlocks,earlier.paidPrecision,earlier.wordRoom,earlier.positiveWord,
    earlier.occupied,earlier.rotations,earlier.matrix,earlier.signedWidth,earlier.snapshotsFit,
    earlier.roleTable,earlier.tailRoom,limit,⟨wide,?_,?_⟩,?_⟩
  · exact stageVenue_frame _ wide _ _ _ limit low _ datedMem m register
      (out.venue.outputs_from_degree (PhysicalReset.FinalInputs.predecessor u) (out.fundedEnd loc) low
        (high.trans centers.1) _) fixed
  · exact (fixed _ (high.trans centers.2.1)).trans num
  · intro x lane
    exact (fixed _ ((high.trans (centers.2.2 _)).trans (Nat.le_add_right ..))).trans (alive x lane)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

import OAI.Hierarchy.DescentIssuedPrimitiveDateRows
import OAI.Hierarchy.DescentProfiledTerminalActorRows

namespace OAI
/-! # The original final date and its paid, actor and signed raster rows -/
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
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192
set_option cleanup.letToHave false
attribute [local irreducible] SeedNamed.issued normalizedPackedChart

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g W q piece : ℕ}
local notation "p" => W*piece
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0< (W*piece)) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
variable (c : ((Epochs.finish G _ _ ((normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten)).choose)).Choice)
local notation "b" => issued X G S ordinary reset branch positive room shorten c
local notation "s" => S.firstWidth G.b p
local notation "Z" => S.grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
open Chronology Chronology.RegisterTimeline DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
attribute [local irreducible] Origin.source Origin.archivePackage RegisterTimeline.position RegisterTimeline.date DateCode.history
open DescentExteriorReplay DescentTerminalFixedSlices DescentSeedRoot DescentActorRaster DescentColonies
open DescentTerminalRoleTables DescentTerminalCombinedRole DescentPackedColony
variable {j rest w : ℕ} (age : 0< S.height) (dateDegree datePayload lo header : ℕ)
  (first : Position) (mem : Memory w) (headerRows paidRows replayBase matrixTable roleBase : ℕ)
  (dateRotation : ℕ→ℕ) (snapshots : Snapshots k) (fit:(S.firstWidth G.b (W*piece))<2^w)
local notation "board" => reset.board
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "ticket" => issuedFinalReset X G S ordinary reset branch positive room shorten c age
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
local notation "menu" => RegisterTimeline.fromProfiles G S board rot k tail p f g R dateDegree datePayload lo header (ch).layout
local notation "ordinaryAt" => (menu).ordinary
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
local notation "dateSpec" => Branch.preflightSpec X G S k g p tail (Branch.geometryFormat G S k g p tail q R rot headerRows paidRows)
local notation "datePorts" => Fintype.card (Port P X.width)
local notation "datePhase" => Phase.scheduled G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
  operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
local notation "dateOut" => (datePhase).output
local notation "dateOrigin" => (datePhase).dateBase
local notation "dateMachine" => PhysicalReset.scheduled G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
  s Z operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
local notation "dateCalendar" => Branch.replayCalendar X S k tail j rest snapshots
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
local notation "roleBankBits" => fun f:Fin 6=>DescentTerminalCombinedRole.width dateColors (max 8 (2^S.capGain))
  (NativeBranch.privateSlotCapacity G S R) p R f*(S.epochPower^S.localTokenExponent)*(dateSpec).groups
local notation "input_" sp:arg => DatePorts.resetInputs G S board k tail dateAge p f g R dateDegree datePayload
  ordinaryAt rot s Z (old).ports (old).floor w sp
local notation "rowsAt" sp:arg m:arg => PrimitiveDateRows (q:=q) (j:=j) (rest:=rest) (W:=W) (piece:=piece) (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive)
    (room:=room) (shorten:=shorten) (c:=c) («board»:=board) («dateAge»:=dateAge) (dateDegree:=dateDegree)
    (datePayload:=datePayload) («ordinaryAt»:=ordinaryAt) («operandLanes»:=operandLanes) («primitiveLanes»:=primitiveLanes)
    («previousDate»:=previousDate) («priorAddress»:=priorAddress) («rosterBank»:=rosterBank) («datedFloor»:=datedFloor)
    (replayBase:=replayBase) (matrixTable:=matrixTable) (dateRotation:=dateRotation)
    (snapshots:=snapshots) (roleBase:=roleBase) (dateInput:=input_ sp) («datedMem»:=m)
    (headerRows:=headerRows) (paidRows:=paidRows)
local notation "physicalRows" sp:arg => rowsAt sp datedMem
include age in
/-- The returned terminal raster is read on the actual calendar chosen from the
packed profile. Its private charge, venue and actor masks share the same history. -/
theorem profiled_terminal_venue (bus:datePayload≤ w) (seedDegree:first.ports.venue.degree=3)
    (degreeRoom:maximumDegree (S.rounds+1)+1<2^w)
    (seed:Geometry G S menu k w 0 first)
    (placed:∀i (e:RunTrace.Events traces i),fitsAt traces menu first (w:=w) i e)
    (words:SnapshotWordRoom S n h k tail p f g datePayload w) (limit:ℕ) (valid:Prop)
    (origin:first.ports.held (b).origin.source first.floor mem)
    (course:OriginalCourse traces menu first c mem limit valid)
    (live:(b).path.selections.length< limit ∨ valid)
    (maskRoom:(dateSpec).maskBase censusBase<2^w) (word:0< w) (shops:0< dateShops)
    (rotations:∀i< S.length,dateRotation i< replayBase)
    (matrix:matrixTable+32*DescentExteriorShelf.span j rest s datePorts≤ replayBase)
    (signed:(dateVenue).signedLanes=S.groupCount S.length)
    (snaps:∀i< S.length,∀bank,snapshots.compact i=some bank→bank.Fits w replayBase)
    (roles:roleBase+DescentTerminalRoleTables.count roleBankBits≤ replayBase)
    (terminal:(cursor S.length).floor≤ replayBase) :
    ∃space,(physicalRows space) ((b).target.terminalRoster (b).target.valid.host) :=by
  have seedAt : Geometry G S menu k w 0 (cursor 0) := by
    simpa only [RegisterTimeline.calendar, RegisterTimeline.position] using seed
  have installed (i:ℕ) (e:RunTrace.Events traces i) :=
    profiled_installed X G S ordinary reset branch positive room shorten w fit board rot tail R dateDegree
      datePayload lo header first seedAt placed i e
  have actors:=profiled_terminal_actor_rows X G S ordinary reset branch positive room shorten w fit R dateDegree
    datePayload lo header first bus seedDegree degreeRoom c mem seedAt placed words limit valid origin course ticket live
  apply issued_primitive_date_rows (X:=X) (G:=G) (S:=S) (q:=q) (W:=W) (piece:=piece)
    (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive)
    (room:=room) (shorten:=shorten) (c:=c) (age:=age) («board»:=board) (dateDegree:=dateDegree)
    (datePayload:=datePayload) (header:=header) (profile:=(menu).profile) (seats:=(menu).seats)
    («ordinaryAt»:=ordinaryAt) (first:=first) (mem:=mem) (headerRows:=headerRows) (paidRows:=paidRows)
    (replayBase:=replayBase) (matrixTable:=matrixTable) (roleBase:=roleBase) (snapshots:=snapshots)
    (limit:=limit) (valid:=valid) (dateRotation:=dateRotation)
    (fixed := fun i a other x y hx hy=>all_registered_moves X G S ordinary reset branch positive room shorten w
      menu rfl rfl rfl i (cursor i) a other x y hx hy)
    (origin:=origin) (runs:=course.advance) (live:=live) (startRooms:=seed.room)
    (installed:=fun i e _=>(installed i e).2)
    actors (installed dateAge ⟨c,(ticket).event⟩).1.format maskRoom word shops rotations matrix signed snaps roles terminal

include age in
/-- The one low-count copy at the end of the dated run preserves the genuine
last register, including every live and padded actor row. -/
theorem profiled_registered_date_rows (bus:datePayload≤ w) (seedDegree:first.ports.venue.degree=3)
    (degreeRoom:maximumDegree (S.rounds+1)+1<2^w)
    (seed:Geometry G S menu k w 0 first)
    (placed:∀i (e:RunTrace.Events traces i),fitsAt traces menu first (w:=w) i e)
    (words:SnapshotWordRoom S n h k tail p f g datePayload w) (limit:ℕ) (valid:Prop)
    (origin:first.ports.held (b).origin.source first.floor mem)
    (course:OriginalCourse traces menu first c mem limit valid)
    (live:(b).path.selections.length< limit ∨ valid)
    (maskRoom:(dateSpec).maskBase censusBase<2^w) (word:0< w) (shops:0< dateShops)
    (rotations:∀i< S.length,dateRotation i< replayBase)
    (matrix:matrixTable+32*DescentExteriorShelf.span j rest s datePorts≤ replayBase)
    (signed:(dateVenue).signedLanes=S.groupCount S.length)
    (snaps:∀i< S.length,∀bank,snapshots.compact i=some bank→bank.Fits w replayBase)
    (roles:roleBase+DescentTerminalRoleTables.count roleBankBits≤ replayBase)
    (terminal:(cursor S.length).floor≤ replayBase)
    (capture count:ℕ) (source:ℕ→ℕ) (below:capture+count≤ first.floor) :
    ∃din:(dateMachine).DateInputs ((dateMachine).stageStart datedFloor) w,
      WideRegisteredDateRows (q:=q) (j:=j) (rest:=rest) (W:=W) (piece:=piece)
        (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch)
        (positive:=positive) (room:=room) (shorten:=shorten) (c:=c) («board»:=board)
        («dateAge»:=dateAge) (dateDegree:=dateDegree) (datePayload:=datePayload) («ordinaryAt»:=ordinaryAt)
        («operandLanes»:=operandLanes) («primitiveLanes»:=primitiveLanes) («previousDate»:=previousDate)
        («priorAddress»:=priorAddress) («rosterBank»:=rosterBank) («datedFloor»:=datedFloor)
        (replayBase:=replayBase) (matrixTable:=matrixTable) (dateRotation:=dateRotation)
        (snapshots:=snapshots) (roleBase:=roleBase) (dateInput:=din)
        (headerRows:=headerRows) (paidRows:=paidRows)
        («datedMem»:=DescentLowCountBook.output capture source datedMem count) :=by
  obtain ⟨space,earned⟩:=profiled_terminal_venue (X:=X) (G:=G) (S:=S) (q:=q) (j:=j)
    (rest:=rest) (W:=W) (piece:=piece) (ordinary:=ordinary) (reset:=reset) (branch:=branch)
    (positive:=positive) (room:=room) (shorten:=shorten) (c:=c) (age:=age) (dateDegree:=dateDegree)
    (datePayload:=datePayload) (lo:=lo) (header:=header) (first:=first) (mem:=mem)
    (headerRows:=headerRows) (paidRows:=paidRows) (replayBase:=replayBase) (matrixTable:=matrixTable)
    (roleBase:=roleBase) (dateRotation:=dateRotation) (snapshots:=snapshots) (fit:=fit)
    bus seedDegree degreeRoom seed placed words limit valid origin course live maskRoom word shops rotations
    matrix signed snaps roles terminal
  have growth:first.floor≤(old).floor:=by
    rw [position_floor steps first dateAge]
    exact DescentDatedAddressBook.floor_mono first.floor (span steps first) (Nat.zero_le dateAge)
  refine ⟨input_ space,?_⟩
  exact issued_primitive_date_rows_after_capture (X:=X) (G:=G) (S:=S) (q:=q) (j:=j)
    (rest:=rest) (W:=W) (piece:=piece) (ordinary:=ordinary) (reset:=reset) (branch:=branch)
    (positive:=positive) (room:=room) (shorten:=shorten) (c:=c) («board»:=board) (dateDegree:=dateDegree)
    (datePayload:=datePayload) (header:=header) («ordinaryAt»:=ordinaryAt) (profile:=(menu).profile)
    (seats:=(menu).seats) (first:=first) (mem:=mem) (headerRows:=headerRows) (paidRows:=paidRows)
    (replayBase:=replayBase) (matrixTable:=matrixTable) (roleBase:=roleBase) (dateRotation:=dateRotation)
    (snapshots:=snapshots) capture count source (below.trans growth) earned

end
end Hierarchy.DescentSixParty.SeedNamed

-- Skip the costly local suggestion index for these large theorem types during export.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun prior =>
  ["profiled_terminal_venue", "profiled_registered_date_rows"] ++ prior

end OAI

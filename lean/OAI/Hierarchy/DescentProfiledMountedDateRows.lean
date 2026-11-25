import OAI.Hierarchy.DescentProfiledTerminalVenue
import OAI.Hierarchy.DescentRoleMountSpan
import OAI.Hierarchy.DescentDatedVenueBelow

namespace OAI
/-! The selected final reset's venue, count and actor rows survive installation of the role tables. -/
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
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192
set_option cleanup.letToHave false
attribute [local irreducible] SeedNamed.issued normalizedPackedChart Origin.source Origin.archivePackage

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
open DescentExteriorReplay DescentTerminalFixedSlices DescentSeedRoot DescentActorRaster DescentColonies
open DescentTerminalRoleTables DescentTerminalCombinedRole DescentPackedColony DescentSIMDLookup
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
attribute [local irreducible] RegisterTimeline.position RegisterTimeline.date DateCode.history issuedFinalReset Path.Event.actorPlanes
/-- The captured counts finish before the actual rebased final reset even after prior
register padding, presence scans and the booked input transpose. -/
theorem scheduled_capture_before (capture count:ℕ) (below : capture+count≤first.floor) :
    capture+count≤dateOrigin :=by
  have low:capture+count≤(old).floor:=by
    apply below.trans
    rw [position_floor steps first dateAge]
    exact DescentDatedAddressBook.floor_mono first.floor (span steps first) (Nat.zero_le dateAge)
  have shift:=((old).ports.resetPad k).cuts (old).floor
  have roots:=(dateMachine).occupied ((dateMachine).stageStart datedFloor)
  have entry0:capture+count≤datedFloor:=(low.trans (shift.1.trans shift.2)).trans (((old).ports.presence k).lower _)
  exact ((entry0.trans ((dateMachine).ingress.after datedFloor)).trans roots.1).trans roots.2.1


local notation "sourceMask" => Venue.actual (b).target.placement (Function.Embedding.refl _)
  ((b).target.vertex.trans (Fin.castLEEmb (b).target.valid.host))
local notation "heldPorts" input:arg => DatePorts.reset dateMachine ((dateMachine).stageStart datedFloor) input
local notation "dateRoof" => (dateMachine).fullEnd datedFloor

private theorem preserved_registered_venue_and_actors
    (u : (dateMachine).DateInputs ((dateMachine).stageStart datedFloor) w)
    (dateLast : dateAge+1=S.length) (preceding : (previousDate).k=k)
    (sourceMem staged target : Memory w) (startAddress : ℕ)
    (start : startAddress≤dateOrigin) (endFit : dateRoof<2^w)
    (wireRoom : (heldPorts u).WireRoom w dateRoof) (countRoom : (heldPorts u).HeaderRoom w dateRoof)
    (keepLo : ∀ a<dateRoof,target a=staged a) (keepHi : ∀ a,startAddress≤a→staged a=sourceMem a)
    (original : (heldPorts u).held (b).target dateRoof sourceMem)
    (alive : ∀x,DescentPackedColony.Reads (actorBank x) (sourceMask x) (S.groupCount S.length) sourceMem) :
    (heldPorts u).held (b).target dateRoof target ∧
      ∀x,DescentPackedColony.Reads (actorBank x) (sourceMask x) (S.groupCount S.length) target :=by
  let pages:=heldPorts u
  let roof:=dateRoof
  have axes:=PhysicalReset.scheduled_terminal_shape G S board k tail dateAge p f g R dateDegree datePayload
    ordinaryAt rot s Z operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor dateLast preceding
  have blocks:pages.venue.k=k:=axes.1
  have groups:pages.venue.groups=S.groupCount S.length:=axes.2.2.1
  have names:=Branch.preflight_caps (tail:=tail) X G S (b) (Branch.geometryFormat G S k g p tail q R rot headerRows paidRows)
  have sockets:(b).target.placement.cap=pages.venue.cap:=names.2.1.trans axes.2.2.2.1.symm
  have centers:=(dateOut).terminal_centers_above dateOrigin
  have registered : ∃ wide : Fintype.card (b).target.V ≤ pages.venue.hosts,
      stageVenue (b).target wide pages.io pages.venue.lanes pages.venue.paidBits roof
        ((b).target.venueRoster wide) sourceMem ∧
            sourceMem pages.archive.count.base=(Fintype.card (b).target.V : Computability.VPVNP.BurstRAM.Word w) := original
  obtain ⟨wide,venue,population⟩:=registered
  have rec₁:=stageVenue_frame _ wide _ _ _ roof startAddress _ sourceMem staged venue
    ((dateOut).venue.outputs_from_degree (PhysicalReset.FinalInputs.predecessor u) ((dateOut).fundedEnd dateOrigin)
      startAddress (start.trans centers.1) _) keepHi
  have countEarly:pages.archive.count.base<roof :=
    (Nat.lt_add_of_pos_right (Nat.two_pow_pos pages.archive.count.bits)).trans_le countRoom.count.2.2
  constructor
  · refine (show ∃ wide : Fintype.card (b).target.V ≤ pages.venue.hosts,
        stageVenue (b).target wide pages.io pages.venue.lanes pages.venue.paidBits roof
          ((b).target.venueRoster wide) target ∧
            target pages.archive.count.base=(Fintype.card (b).target.V : Computability.VPVNP.BurstRAM.Word w) from ⟨wide,?_,?_⟩)
    · apply stageVenue_below _ wide _ _ _ roof _ staged target rec₁ _ keepLo
      intro x i
      have capRows:=wireRoom (Fin.cast (congrArg (2^·) blocks.symm) x) (Fin.cast (congrArg (2*·) sockets) i)
      have footprint := congrArg (fun g => pages.venue.hosts * DescentSIMDLookup.chunks g pages.venue.lanes) groups
      exact (Nat.add_le_add_left (footprint.symm.trans_le capRows.2) _).trans capRows.1.2.2
    · exact (keepLo _ countEarly).trans ((keepHi _ (start.trans centers.2.1)).trans population)
  · intro x row_
    have tailRoom:(dateOut).fullEnd dateOrigin≤roof:=(dateOut).venue_before_metadata dateOrigin
    have support:=(dateOut).terminal_actor_room dateOrigin (tailRoom.trans_lt endFit)
      (Fin.cast (congrArg (2^·) blocks.symm) x)
    have fitRows:(row (S.hostSize S.length) (S.groupCount S.length) (S.groupCount S.length) row_).val<
        ((actorBank) x).size:=by
      apply (row _ _ _ row_).isLt.trans_le
      have footprint := congrArg₂ Nat.mul axes.2.1
        (congrArg₂ DescentSIMDLookup.chunks axes.2.2.1 axes.2.2.2.2)
      exact footprint.symm.trans_le support.2
    exact (keepLo _ ((Nat.add_lt_add_left fitRows _).trans_le (support.1.trans tailRoom))).trans
      ((keepHi _ ((start.trans (centers.2.2 _)).trans (Nat.le_add_right ..))).trans (alive x row_))


attribute [local irreducible] DatePorts.held

include age in
theorem profiled_mounted_date_rows (bus:datePayload≤ w) (seedDegree:first.ports.venue.degree=3)
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
    (capture count:ℕ) (source:ℕ→ℕ) (below:capture+count≤ first.floor)
    (mount:RoleMount w roleBase replayBase) (beforeRom:(cursor S.length).floor≤roleBase) :
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
        («datedMem»:=mount.phase.image (DescentLowCountBook.output capture source datedMem count)):=by
  have seedAt : Geometry G S menu k w 0 (cursor 0) := by
    simpa only [RegisterTimeline.calendar, RegisterTimeline.position] using seed
  have fixed : ∀i (a other:RunTrace.Events traces i) (x y:Move w),
      steps i a (cursor i) x→steps i other (cursor i) y→x=y  := fun i a other x y hx hy=>all_registered_moves X G S ordinary reset branch positive room shorten w
    menu rfl rfl rfl i (cursor i) a other x y hx hy
  have installed (i:ℕ) (e:RunTrace.Events traces i) :=
    profiled_installed X G S ordinary reset branch positive room shorten w fit board rot tail R dateDegree
      datePayload lo header first seedAt placed i e
  have actors:=profiled_terminal_actor_rows X G S ordinary reset branch positive room shorten w fit R dateDegree
    datePayload lo header first bus seedDegree degreeRoom c mem seedAt placed words limit valid origin course ticket live
  obtain ⟨chosen,paid,paidRoof,_⟩:=(installed dateAge ⟨c,(ticket).event⟩).2
  have originAt : first.ports.held (traces c).first first.floor mem := by
    simpa only [traceAt] using origin
  have traceLive : (traces c).path.selections.length<limit ∨ valid := by
    simpa only [traceAt] using live
  have present : ∃mv,steps dateAge ⟨c,(ticket).event⟩ (old) mv := ⟨chosen,paid⟩
  have lastData := last_reset_register traces menu first c mem limit valid fixed
    originAt course.advance ticket traceLive present actors
  obtain ⟨cap,space,_,pos,held,alive⟩:=lastData
  let u:=input_ space
  let machine:=dateMachine
  let pages:=DatePorts.reset machine (machine.stageStart datedFloor) u
  let roof:=machine.fullEnd datedFloor
  let m₁:=DescentLowCountBook.output capture source datedMem count
  let dst:=mount.phase.image m₁
  have original:pages.held (b).target roof datedMem:=held
  have floorEq:(cursor S.length).floor=roof:=congrArg Position.floor pos
  have before:roof≤roleBase:=floorEq.ge.trans beforeRom
  have nextRoom:Rooms G S menu k w S.length (cursor S.length):=by
    have after_:=next_room traces menu first fixed (fun i e _=>(installed i e).2) dateAge
      ⟨c,(ticket).event⟩ (installed dateAge ⟨c,(ticket).event⟩).1.room
    rwa [(ticket).succ_age] at after_
  rw [pos] at nextRoom
  have wireRoom:pages.WireRoom w roof:=nextRoom.wires
  have countRoom:pages.HeaderRoom w roof:=nextRoom.header
  have fmt:=(installed dateAge ⟨c,(ticket).event⟩).1.format
  have endFit:roof<2^w:=by
    have eqn:=returned traces menu first dateAge ⟨c,(ticket).event⟩ chosen paid
      (fun d t h=>fixed dateAge d ⟨c,(ticket).event⟩ t chosen h paid)
    have eqpos:cursor S.length=chosen.next:=by simpa only [(ticket).succ_age] using eqn.2
    calc
      roof=(cursor S.length).floor:=floorEq.symm
      _=chosen.next.floor:=congrArg Position.floor eqpos
      _<2^w:=paidRoof
  have start:capture+count≤dateOrigin:=by
    apply scheduled_capture_before (capture:=capture) (count:=count)
    exact below
  have keepLo (a:ℕ) (lt:a<roof) : dst a=m₁ a:=mount.frame m₁ a (.inl (lt.trans_le before))
  have keepHi (a:ℕ) (le:capture+count≤a) : m₁ a=datedMem a:=
    DescentLowCountBook.frame capture source datedMem count a (.inr le)
  refine ⟨u,rfl,(ticket).succ_age,fmt.width,fmt.paid,maskRoom,word,shops,rotations,matrix,signed,snaps,roles,
    floorEq.ge.trans terminal,roof,?_⟩
  exact preserved_registered_venue_and_actors (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset)
    (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (c:=c) (first:=first)
    (W:=W) (piece:=piece) (q:=q) (dateDegree:=dateDegree) (datePayload:=datePayload) (lo:=lo)
    (header:=header) (headerRows:=headerRows) (paidRows:=paidRows) (fit:=fit)
    u (ticket).succ_age fmt.width datedMem m₁ dst (capture+count) start endFit
    wireRoom countRoom keepLo keepHi original alive

end
end Hierarchy.DescentSixParty.SeedNamed

-- Skip the costly local suggestion index for these large theorem types during export.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun prior =>
  ["profiled_mounted_date_rows"] ++ prior

end OAI

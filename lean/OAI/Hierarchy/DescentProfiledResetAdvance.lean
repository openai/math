import OAI.Hierarchy.DescentScheduledReachedVenue
import OAI.Hierarchy.DescentProfiledResetControls
import OAI.Hierarchy.DescentProfiledSnapshotWordRoom
import OAI.Hierarchy.DescentScheduledCutPower

namespace OAI
/-! # A real profiled reset advances the signed and paid calendar in one common memory -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentSixParty DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentSIMDLookup DescentResetGates
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
open scoped Fin.CommRing
set_option cleanup.letToHave false
variable {F P : Type} [Field F] [Fintype P] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z D n₁ h₁ C f₁ g₁ cut tail₁ wire hist : ℕ}
    {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n₁ h₁ C f₁ g₁ cut tail₁}
    {n h f g tail : ℕ} (board₀ : NonlinearExpanders.Graph n h) (op₀ : RotorSpec)
    (B : ClosedReset input ctl) (p drift degree payload w : ℕ) (ordinary : ℕ→Dated.Ordinary)
    (seats profile : ℕ→ℕ) (header : ℕ) (cursor : Position)
local notation "op" => op₀
local notation "s₀" => S.firstWidth G.b p
local notation "Z₀" => S.grainAt G.b p 0
local notation "board" => board₀
local notation "old" => cursor.ports.venue
local notation "io" => cursor.ports.io
local notation "cap" => ((capCalendar G.b S.rounds g S.height).take age).prod*256
local notation "oldExp" => NativePitch.resetCut S k tail p f payload age
local notation "nextM" => NativePitch.incoming S k tail p f payload ordinary (age+1)
local notation "oldL" => cursor.ports.operandLanes
local notation "roleL" => cursor.ports.roleLanes
local notation "token" => DescentPrimitivePalette.printedBits G s₀ Z₀ op
local notation "rcut" => receiverCut G S board k tail age p f g drift degree payload oldExp nextM (op).C (op).w
  oldL roleL token old
local notation "base" => cursor.ports.priorStart k cursor.floor
local notation "history" => (cursor.ports.afterPad k cursor.floor).archive
local notation "outer" => scheduledAtPorts G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor
local notation "a" => (outer).inner
local notation "v" => (a).successor
local notation "start" => (a).stageStart base
local notation "E" => (a).estimator start
local notation "HH" => S.hostSize age
local notation "Ht" => GroupStage.depthBound (old).degree n f g
local notation "amp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap
local notation "fits" => scheduled_cut_origin G S board k tail age p f g drift degree payload ordinary op s₀ Z₀ oldL roleL old
local notation "priorFits" => preceding_cut S k tail p f payload age
local notation "menu" => (⟨board,op,g,tail,p,f,drift,degree,payload,seats,ordinary,profile,header⟩ : Menu n h)
local notation "publisher" => priorArchivePhase G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w
variable (capacity : cursor.ports.venue.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256)
    (space : ScheduledCodeRoom G S board₀ k tail age p f g drift degree payload ordinary op₀ (S.firstWidth G.b p) (S.grainAt G.b p 0)
      cursor.ports.operandLanes cursor.ports.roleLanes cursor.ports.venue cursor.ports.io (cursor.ports.priorStart k cursor.floor) w
      (cursor.ports.afterPad k cursor.floor).archive)
local notation "u" => DatePorts.resetInputs G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w space
local notation "finish" => FinalInputs.fromArchive G S board k tail age p f g drift degree payload rcut oldExp (2^rcut)
  nextM (op).C (op).w oldL roleL token old io base w fits fits priorFits (history).count
  (NamedCodeRoom.prepared space) (NamedCodeRoom.scene space) history s₀ Z₀ op capacity
local notation "move" => resetMove (G:=G) (S:=S) menu k age w cursor capacity space

private theorem runsAtHistory {w : ℕ} (program : ℕ → DateCode w) (boot : Memory w) (age : ℕ)
    (action : DateCode w) (chosen : program age = action) {rest : Memory w → Memory w → Prop}
    (runs : ∀m, ∃dst,action.Runs m dst ∧ rest m dst) :
    action.Runs (DateCode.history program boot age) (DateCode.history program boot (age+1)) := by
  let src := DateCode.history program boot age
  obtain ⟨out,run,_⟩ := runs src
  change action.Runs src ((program age).nextMemory src)
  rw [chosen,DateCode.nextMemory_eq _ run]
  exact run

omit [Fintype P] in
private theorem calibratedResetVenue {len : ℕ} (tr : RunTrace G q ε S k wire hist len bits d)
    (before : Path tr.first input) (after_ : Path B.next tr.last) (joined : (before.reset B).append after_=tr.path)
    (geo : Geometry G S menu k w age cursor)
    (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (hb : HEq ctl.board board₀) (ho : RotorSpec.ofRates ctl=op₀) (degreeD : D=atRound S.rounds)
    (prepared : ScheduledReady G S board₀ k tail age p f g drift degree payload ordinary op₀ s₀ Z₀ oldL roleL old io base w history capacity space)
    (calendar_ : ℕ → DateCode w) (boot : Memory w)
    (chosen : calendar_ age = (move).code)
    (padded : (publisher).Runs (DateCode.history calendar_ boot age))
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (histAt : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain) (positive : 0<p) (accepted : B.Recorded p) (elapsed : 0<age) (sorted : SourceSorted W input.order)
    (oldCap : cursor.ports.venue.cap=input.placement.cap)
    (seen : stageVenue input input.valid.host io cursor.ports.venue.lanes cursor.ports.venue.paidBits base
      (input.venueRoster input.valid.host) ((publisher).image (DateCode.history calendar_ boot age)))
    (counted : (publisher).image (DateCode.history calendar_ boot age) cursor.ports.archive.count.base=(Fintype.card input.V : Computability.VPVNP.BurstRAM.Word w))
    (tag : ((kindCalendar S.rounds S.height).drop age).head? = some true)
    (high : (outer).fullEnd<2^w) (narrow : 8*(menu).receiverWidth G S k age cursor.ports≤payload)
    (bus : payload≤w) (words : SnapshotWordRoom S n h k tail p f g payload w) :
    ((move).next.ports.held B.next (move).next.floor (DateCode.history calendar_ boot (age+1))) ∧
    (nextM=S.groupCount (age+1) →
      ((Path.Event.reset before B after_ joined : tr.path.Event age)).actorPlanes
        (fun (x : DescentColonies.Block k)=>(v).terminalActor ((a).rebased start) x.val) (DateCode.history calendar_ boot (age+1))) := by
  have narrowAt : 8*(v).groupWidth≤payload := (Nat.mul_le_mul_left 8 ((menu).receiverWidth_at G S k age cursor.ports base).le).trans narrow
  have rootBound := (menu).receiverCut_pow_le G S k age cursor.ports w narrow bus
  subst n₁
  subst h₁
  subst f₁
  subst g₁
  subst tail₁
  have sameBoard : ctl.board=board₀ := eq_of_heq hb
  subst board₀
  subst op₀
  have round:=reset_slot_index S.rounds S.height age tag
  have atDegree : cursor.ports.venue.degree=D:=geo.degree.trans ((congrArg atRound round).trans degreeD.symm)
  have come:=geo.format.pitch B.age
  rw [NativePitch.incoming,ite_eq_left B.age,ite_eq_left round] at come
  have sites : 0<S.initialSites:=by obtain ⟨t,ht⟩:=geo.room.initialSites; rw [ht]; positivity
  have launched := DateInputs.scheduled_reached_venue (input:=input) (ctl:=ctl) (p:=p) (path:=tr.path) B before after_ joined accepted drift degree payload ordinary
    s₀ Z₀ cursor.ports cursor.floor w capacity space calendar_ boot prepared gr fee histAt branch positive
    elapsed sorted atDegree oldCap geo.room.hosts geo.room.population.groups geo.format.width geo.format.paid come
    geo.room.header geo.room.wires geo.room.paid seen counted sites bus narrowAt high (words.lanes age B.age.le)
    (by rw [atDegree,degreeD]; exact words.estimator age B.age.le)
    (by rw [degreeD]; exact words.actor) rootBound chosen padded
  exact launched
end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline DescentExteriorReplay ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000
set_option cleanup.letToHave false
attribute [local irreducible] normalizedPackedChart SeedNamed.issued Origin.source Origin.archivePackage
local notation "cert" => SeedNamed.normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "trace" => SeedNamed.issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : s < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentPacking.PackedMatch.Local.Stage
variable (drift degree payload lo header : ℕ) (initial : RegisterTimeline.Position)
local notation "board" => reset.board
local notation "op" => RotorSpec.ofRates reset
local notation "frozen" => tail
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial
local notation "resetAt" => fun i (a:RegisterTimeline.Position)=>
  PhysicalReset.scheduledAtPorts G S board k frozen i p f g drift degree payload (menu).ordinary op
    (S.firstWidth G.b p) (S.grainAt G.b p 0) (a).ports (a).floor

local notation:max "data" j:arg => Geometry G S menu k w j (cursor j)
local notation "program" => RegisterTimeline.instruction (w:=w) traces menu initial

variable (bus : payload≤w) (seedDegree : initial.ports.venue.degree=3)
    (degreeRoom : maximumDegree (S.rounds+1)+1<2^w)

variable (walk : (last).Choice) (m : Memory w)
variable {U : MarkedWorld F 0 pins widths} {i z D : ℕ}
  {r : Reached U G price fee S k i z D (S.epochPower^S.priceExponent) s}
  {n₁ h₁ C₁ f₁ g₁ cut₁ tail₁ : ℕ} {ctl : ResetRates G S k D n₁ h₁ C₁ f₁ g₁ cut₁ tail₁}
  (before : Path (traces walk).first r) (B : ClosedReset r ctl)
  (after_ : Path B.next (traces walk).last) (joined : (before.reset B).append after_=(traces walk).path)
local notation "evt" => (Path.Event.reset before B after_ joined : (traces walk).path.Event i)
local notation "cur" => cursor i
local notation "history" => DateCode.history program m i
local notation "padEnd" => (cur).ports.priorStart k (cur).floor

local notation "issue" => RegisterTimeline.issued (w:=w) traces menu
local notation "afterPitch" => NativePitch.incoming S k tail p f payload (menu).ordinary (i+1)
local notation "inner₁" => (resetAt i cur).inner
local notation "afterFloor" => (inner₁).rebased ((inner₁).stageStart padEnd)
local notation "actorRows" => (fun (x:DescentColonies.Block k)=>(inner₁).successor.terminalActor afterFloor x.val)

include before after_ joined in
private theorem controlsForResetAdvance :
    B.Recorded p ∧ RotorSpec.ofRates ctl=op ∧ tail₁=tail ∧ 0 < i ∧
      SourceSorted U r.order ∧ z=S.grainAt G.b p (i+1) := by
  exact profiled_reset_controls (r:=r) (ctl:=ctl) X G S ordinary reset branch positive room shorten walk before B after_ joined

private theorem tagsForResetAdvance : ∀x,(traces x).path.kinds=kindCalendar S.rounds S.height := fun x=>(trace x).kinds

attribute [local irreducible] traceAt DateCode.Runs
include bus seedDegree degreeRoom in
theorem profiled_reset_published (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (words : SnapshotWordRoom S n h k tail p f g payload w)
    (incoming : Path.Event.incoming (t:=traces walk) evt cur history) :
    (∃mv : Move w,issue i ⟨walk,evt⟩ cur mv ∧ ∃dst,mv.code.Runs history dst ∧
      Path.Event.outgoing (t:=traces walk) evt mv.next dst) ∧
    (afterPitch=S.groupCount (i+1)→(evt).actorPlanes actorRows (DateCode.history program m (i+1))) :=by
  obtain ⟨certified,operator,sameTail,elapsed,sorted,grain⟩:=
    controlsForResetAdvance X G S ordinary reset branch positive room shorten walk before B after_ joined
  obtain ⟨shapeN,shapeH,shapeC,shapeF,shapeG,degreeD,packet,originalBoard⟩:=
    rotor_control_fields G S ctl reset operator
  obtain ⟨geo,space,prepared,chosen,nextFloor,tag,high,narrow,padded,oldCap,census,seen⟩:=
    profiled_reset_entry X G S ordinary reset branch positive room shorten w fit board op frozen
      drift degree payload lo header initial bus seedDegree degreeRoom walk m before B after_ joined seed₁ placed₁ incoming
  have native := RegisterTimeline.calibratedResetVenue board op B p drift degree payload w
    (menu).ordinary (menu).seats (menu).profile (menu).header cur geo.capacity space (traces walk) before after_ joined geo
    shapeN shapeH shapeF shapeG sameTail originalBoard operator degreeD prepared program m chosen padded
    grain rfl rfl branch positive certified elapsed sorted oldCap seen census tag high narrow bus words
  let ev:RunTrace.Events traces i:=⟨walk,evt⟩
  have round:=reset_slot_index S.rounds S.height i tag
  have atDegree : (cur).ports.venue.degree=D:=geo.degree.trans ((congrArg atRound round).trans degreeD.symm)
  have steps:=RegisterTimeline.reset_issued_any traces menu initial (tagsForResetAdvance X G S ordinary reset branch positive room shorten) i ev rfl geo narrow bus
    (atDegree.symm ▸ (degreeD.symm ▸ words.actor.successor)) high
  obtain ⟨mv,proves,roof,any⟩:=steps
  unfold RegisterTimeline.issued at proves
  obtain ⟨other,sp₁,rfl⟩:=proves
  have executed := RegisterTimeline.runsAtHistory program m i _ chosen any
  refine ⟨?_,native.2⟩
  exact ⟨_,⟨other,sp₁,rfl⟩,DateCode.history program m (i+1),executed,native.1⟩


include bus seedDegree degreeRoom in
theorem profiled_last_actor_planes (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (words : SnapshotWordRoom S n h k tail p f g payload w)
    (incoming : Path.Event.incoming (t:=traces walk) evt cur history) (atLast : i+1=S.length) :
    (evt).actorPlanes actorRows (DateCode.history program m (i+1)) :=by
  apply (profiled_reset_published X G S ordinary reset branch positive room shorten w fit drift degree payload lo
    header initial bus seedDegree degreeRoom walk m before B after_ joined seed₁ placed₁ words incoming).2
  rw [atLast,NativePitch.terminal]

include bus seedDegree degreeRoom in
theorem profiled_reset_advance (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (words : SnapshotWordRoom S n h k tail p f g payload w) (limit : ℕ) (valid : Prop) :
    RegisterTimeline.advances traces menu initial walk m limit valid i evt :=by
  intro incoming _
  exact (profiled_reset_published X G S ordinary reset branch positive room shorten w fit drift degree payload lo
    header initial bus seedDegree degreeRoom walk m before B after_ joined seed₁ placed₁ words incoming).1

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

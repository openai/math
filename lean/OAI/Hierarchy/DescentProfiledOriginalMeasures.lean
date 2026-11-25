import OAI.Hierarchy.DescentOriginalResetMeasures
import OAI.Hierarchy.DescentProfiledResetOperandPanels

namespace OAI
/-! # Reached original inputs of the chronological reset -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentSixParty DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentSIMDLookup DescentResetGates
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
open scoped Fin.CommRing
set_option cleanup.letToHave false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
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

open private profiledRoomFields from OAI.Hierarchy.DescentProfiledResetRankOperand

include capacity in
private theorem calibratedProfiledMeasures (geo : Geometry G S menu k w age cursor)
    (hg : g₁=g) (degreeD : D=atRound S.rounds) (memory : Memory w)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (histAt : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain) (positive : 0<p)
    (oldCap : cursor.ports.venue.cap=input.placement.cap)
    (seen : stageVenue input input.valid.host io cursor.ports.venue.lanes cursor.ports.venue.paidBits base
      (input.venueRoster input.valid.host) ((publisher).image memory))
    (counted : (publisher).image memory cursor.ports.archive.count.base=(Fintype.card input.V : Computability.VPVNP.BurstRAM.Word w))
    (tag : ((kindCalendar S.rounds S.height).drop age).head? = some true)
    (high : (outer).fullEnd<2^w) (narrow : 8*(menu).receiverWidth G S k age cursor.ports≤payload)
    (bus : payload≤w) (words : SnapshotWordRoom S n h k tail p f g payload w)
    (elapsed : 0<age) (sorted : SourceSorted W input.order) :
    OriginalMeasures (f:=f) (g:=g) (tail:=tail) board₀ op₀ B p drift degree payload w ordinary cursor memory := by
  have round:=reset_slot_index S.rounds S.height age tag
  have atDegree : cursor.ports.venue.degree=D:=geo.degree.trans ((congrArg atRound round).trans degreeD.symm)
  have come:=geo.format.pitch B.age
  rw [NativePitch.incoming,ite_eq_left B.age,ite_eq_left round] at come
  have oldPos : 0<cursor.ports.venue.lanes:=come.symm ▸ Nat.two_pow_pos _
  have capAt:=oldCap.symm.trans capacity
  have live := (ClosedReset.Window.posted_census_limits B p positive gr fee branch (by rw [hg]; exact capAt)).1
  have steps : cursor.floor≤base := (outer).stages.1
  have headroom := geo.room.header.mono steps
  have rooms := profiledRoomFields (e₀:=base) geo steps oldCap
  have acquired := (a).occupied ((a).stageStart base)
  have entryFits : (a).stageStart base < 2^w := ((acquired.1.trans acquired.2.1).trans acquired.2.2).trans_lt high
  have ⟨score,head,host⟩:=PhysicalReset.scheduled_estimator_words G S board₀ k tail age p f g drift degree
    payload ordinary op₀ s₀ Z₀ cursor.ports cursor.floor w (by rw [atDegree,degreeD]; exact words.estimator age B.age.le)
  have actor : ResetActorWords h cursor.ports.venue.degree n k f g w:=by rw [atDegree,degreeD]; exact words.actor
  constructor
  · exact gr
  · exact fee
  · exact capAt
  · exact histAt
  · exact branch
  · exact seen
  · exact headroom.count
  · exact counted
  · exact rooms.2.2
  · exact oldPos
  · exact geo.format.paid
  · exact entryFits
  · exact words.lanes age B.age.le
  · exact score
  · exact live
  · exact actor.degree
  · exact head
  · exact host
  · exact actor.ranks
  · exact actor.actor
  · exact actor.successor
  · exact (menu).receiverCut_pow_le G S k age cursor.ports w narrow bus
  · exact rooms.2.1
  · exact come
  · exact (Nat.mul_le_mul_left 8 ((menu).receiverWidth_at G S k age cursor.ports base).le).trans narrow
  · exact bus
  · exact high
  · exact elapsed
  · exact sorted
  · exact actor.board
  · exact geo.room.population.groups
  · exact geo.room.hosts
  · exact geo.format.width
  · exact B.next.valid.host

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

/-! ## The selected reset on the profiled execution -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
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

local notation "inner₁" => (resetAt i cur).inner

include before after_ joined in
private theorem controlsOnProfiledTrace :
    B.Recorded p ∧ RotorSpec.ofRates ctl=op ∧ tail₁=tail ∧ 0 < i ∧
      SourceSorted U r.order ∧ z=S.grainAt G.b p (i+1) := by
  exact profiled_reset_controls (r:=r) (ctl:=ctl) X G S ordinary reset branch positive room shorten walk before B after_ joined

attribute [local irreducible] traceAt
include bus seedDegree degreeRoom in
theorem profiled_original_measures (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (incoming : Path.Event.incoming (t:=traces walk) evt cur history) (words : SnapshotWordRoom S n h k tail p f g payload w) :
    RegisterTimeline.OriginalMeasures (f:=f) (g:=g) (tail:=tail) board op B p drift degree payload w (menu).ordinary cur history := by
  obtain ⟨recorded,operator,sameTail,elapsed,sorted,grain⟩:=
    controlsOnProfiledTrace X G S ordinary reset branch positive room shorten walk before B after_ joined
  obtain ⟨shapeN,shapeH,shapeC,shapeF,shapeG,degreeD,packet,originalBoard⟩:=
    rotor_control_fields G S ctl reset operator
  obtain ⟨geo,space,prepared,chosen,nextFloor,tag,high,narrow,padded,oldCap,census,seen⟩:=
    profiled_reset_entry X G S ordinary reset branch positive room shorten w fit board op frozen
      drift degree payload lo header initial bus seedDegree degreeRoom walk m before B after_ joined seed₁ placed₁ incoming
  exact RegisterTimeline.calibratedProfiledMeasures board op B p drift degree payload w
    (menu).ordinary (menu).seats (menu).profile (menu).header cur geo.capacity geo
    shapeG degreeD history
    grain rfl rfl branch positive oldCap seen census tag high narrow bus words elapsed sorted

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

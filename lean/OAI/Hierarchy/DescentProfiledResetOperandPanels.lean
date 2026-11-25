import OAI.Hierarchy.DescentProfiledResetRankOperand
import OAI.Hierarchy.DescentMatchedPublicOrigins
import OAI.Hierarchy.DescentScheduledPanelTransport
import OAI.Hierarchy.DescentRegisterEmittedRoleRows
import OAI.Hierarchy.DescentRegisterResetRolePitch

namespace OAI
open private controlsOnProfiledTrace from OAI.Hierarchy.DescentProfiledResetRankOperand

/-! # Transporting the selected menu to its original reset board -/
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

private theorem profiledRoomFields {F₀ : Type} [Field F₀] {G₀ : PoweredGadget F₀} {S₀ : AtomSchedule}
    {n₀ d₀ k₀ w₀ i₀ e₀ c₀ : ℕ} {b₀ : RegisterTimeline.Menu n₀ d₀} {a₀ : RegisterTimeline.Position}
    (geo : RegisterTimeline.Geometry G₀ S₀ b₀ k₀ w₀ i₀ a₀)
    (floorLe : a₀.floor≤e₀) (widthEq : a₀.ports.venue.cap=c₀) :
    0<S₀.hostSize i₀ ∧ S₀.hostSize i₀≤a₀.ports.io.hubs.size ∧
    ∀(x : DescentColonies.Block k₀) (j : Fin (2*c₀)), (a₀.ports.io.wire x.val j.val).Fits w₀ e₀ ∧
      S₀.hostSize i₀ * DescentSIMDLookup.chunks (S₀.groupCount i₀) a₀.ports.venue.lanes≤
      (a₀.ports.io.wire x.val j.val).size := by
  have h := geo.room.hosts
  have g := geo.room.population.groups
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨d, e⟩ := geo.room.initialSites
    rw [AtomSchedule.hostSize, e, geo.room.radix]
    positivity
  · rw [←h]
    exact geo.room.header.hosts
  · intro x j
    have raw := (geo.room.wires.mono floorLe)
      (x.cast (congrArg (2^·) geo.format.width).symm) (j.cast (congrArg (2*·) widthEq).symm)
    simp only [h, g, Fin.val_cast] at raw
    exact raw

include B in
private theorem calibratedPanelFacts (goal : Prop) (geo : Geometry G S menu k w age cursor)
    (hg : g₁=g) (degreeD : D=atRound S.rounds)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) (positive : 0<p) (oldCap : cursor.ports.venue.cap=input.placement.cap)
    (tag : ((kindCalendar S.rounds S.height).drop age).head? = some true)
    (high : (outer).fullEnd<2^w) (narrow : 8*(menu).receiverWidth G S k age cursor.ports≤payload)
    (bus : payload≤w) (words : SnapshotWordRoom S n h k tail p f g payload w)
    (useFields : ∀ (_degreeAt : (old).degree=D) (_capAt : input.placement.cap=cap)
    (_popFit : (history).count.Fits w base)
    (_wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),(cursor.ports.io.wire x.val j.val).Fits w base ∧
      HH*chunks (S.groupCount age) (v).funded.oldLanes≤(cursor.ports.io.wire x.val j.val).size)
    (_oldPos : 0<(v).funded.oldLanes) (_oldWidth : (v).funded.precision=S.censusBits p)
    (_entryFits : start<2^w) (_low : k≤(E).low)
    (_score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (_live : 0 < amp) (_degreePos : 0 < 32*Nat.clog 2 (2*cursor.ports.venue.degree))
    (_headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p) ≤ w) (_hostBits : HH < 2^w)
    (_ranksFit : cursor.ports.venue.degree*2^Ht < 2^w)
    (_namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*cursor.ports.venue.degree)) g n ≤ w)
    (_degFit : cursor.ports.venue.degree+1 < 2^w) (_laneRoom : 2^rcut ≤ w)
    (_hubSpan : HH≤ (io).hubs.size) (_pitchOld : (old).lanes=2^oldExp)
    (_narrow : 8*(v).groupWidth≤payload)
    (_boardRoom : h≤2^k) (_hostPos : 0<S.hostSize age) (_newFit : S.hostSize (age+1)≤2^w), goal) : goal := by
  have round:=reset_slot_index S.rounds S.height age tag
  have atDegree : cursor.ports.venue.degree=D:=geo.degree.trans ((congrArg atRound round).trans degreeD.symm)
  have come:=geo.format.pitch B.age
  rw [NativePitch.incoming,ite_eq_left B.age,ite_eq_left round] at come
  have oldPos : 0<cursor.ports.venue.lanes:=come.symm ▸ Nat.two_pow_pos _
  have capAt:=oldCap.symm.trans geo.capacity
  have live := (ClosedReset.Window.posted_census_limits B p positive gr fee branch (by rw [hg]; exact capAt)).1
  have steps : cursor.floor≤base := (outer).stages.1
  have headroom := geo.room.header.mono steps
  have rooms := profiledRoomFields (e₀:=base) geo steps oldCap
  have acquired := (a).occupied ((a).stageStart base)
  have entryFits : (a).stageStart base < 2^w := ((acquired.1.trans acquired.2.1).trans acquired.2.2).trans_lt high
  have ⟨score,head,host⟩:=PhysicalReset.scheduled_estimator_words G S board₀ k tail age p f g drift degree
    payload ordinary op₀ s₀ Z₀ cursor.ports cursor.floor w (by rw [atDegree,degreeD]; exact words.estimator age B.age.le)
  have actor : ResetActorWords h cursor.ports.venue.degree n k f g w:=by rw [atDegree,degreeD]; exact words.actor
  have narrowAt : 8*(v).groupWidth ≤ payload :=
    (Nat.mul_le_mul_left 8 ((menu).receiverWidth_at G S k age cursor.ports base).le).trans narrow
  exact useFields atDegree capAt headroom.count rooms.2.2 oldPos geo.format.paid entryFits
    (words.lanes age B.age.le) score live actor.degree head host actor.ranks actor.actor actor.successor
    ((menu).receiverCut_pow_le G S k age cursor.ports w narrow bus) rooms.2.1 come narrowAt
    actor.board rooms.1 (words.estimator (age+1) B.age).host.le
end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d) {n degree : ℕ} (b : Menu n degree)
    (initial : Position) (i : ℕ) (e : RunTrace.Events traces i)
local notation "pos" => calendar (w:=w) traces b initial i
local notation "nextPos" => calendar (w:=w) traces b initial (i+1)
local notation "ports" => (pos).ports
local notation "s₀" => S.firstWidth G.b b.p
local notation "Z₀" => S.grainAt G.b b.p 0
local notation "floor₀" => (ports).priorStart k (pos).floor
local notation "prior₀" => ((ports).afterPad k (pos).floor).archive
local notation "outer" => scheduledAtPorts G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload b.ordinary b.op s₀ Z₀ (ports) (pos).floor
local notation "receiver" => (outer).inner.successor.receiver
local notation "codes" => instruction (w:=w) traces b initial
local notation "cap" => ((capCalendar G.b S.rounds b.gain S.height).take i).prod*256

open DescentPackedColony DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks DescentPrimitivePalette
variable {U : MarkedWorld F d P bits} {z D n₁ h₁ C₁ f₁ g₁ cut₁ tail₁ : ℕ}
    {r : Reached U G q ε S k i z D wire hist} {ctl : ResetRates G S k D n₁ h₁ C₁ f₁ g₁ cut₁ tail₁}
    (B : ClosedReset r ctl) {description : BitDescription U} {R : ℕ} (number : Local description)
    (bounds : DatePorts.RangeRoom (ports) r description) (shape : WorldShape b.p R description)
    (label : NodeOrder.All description→Label G s₀ Z₀ b.op)
local notation "support₁" => ScheduledCodeRoom G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
  b.payload b.ordinary b.op s₀ Z₀ (ports).operandLanes (ports).roleLanes (ports).venue (ports).io floor₀ w prior₀
local notation "ready₁" cap₁:arg sp:arg => ScheduledReady G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
    b.payload b.ordinary b.op s₀ Z₀ (ports).operandLanes (ports).roleLanes (ports).venue (ports).io floor₀ w prior₀ cap₁ sp
local notation "issued₁" cap₁:arg sp:arg => DatePorts.resetDate G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
    b.payload b.ordinary b.op s₀ Z₀ (ports) (pos).floor w cap₁ sp
local notation "panel" shape₁:arg sp:arg => MatchedRegisteredOperandPanels b.board b.op B b.p b.drift b.degreeLimit b.payload w
  b.ordinary b.seats b.profile b.header (pos) sp number bounds shape label shape₁ ((shape₁).room.archive)
local notation "publicRows" sp:arg => MatchedPublicRows b.board b.op B b.p b.drift b.degreeLimit b.payload w b.ordinary (pos) sp

local notation "publicOrigins" sp:arg => MatchedPublicOrigins b.board b.op B b.p b.drift b.degreeLimit b.payload w b.ordinary (pos) sp
set_option maxHeartbeats 600000

omit [Fintype P] in
private theorem issuedPanelsOfOriginal (boot : Memory w) (original : ∃(geo : Geometry G S b k w i (pos)) (space : support₁) (admitted : ready₁ geo.capacity space),
      (codes) i=issued₁ geo.capacity space ∧ (nextPos).floor=(outer).fullEnd ∧
      (outer).fullEnd<2^w ∧ 8*b.receiverWidth G S k i (ports)≤b.payload ∧
      ∃(hn : n₁=n) (hh : h₁=degree) (hf : f₁=b.f) (hg : g₁=b.gain) (ht : tail₁=b.tail)
        (hb : HEq ctl.board b.board) (ho : RotorSpec.ofRates ctl=b.op) (degreeAt : (ports).venue.degree=D)
        (capAt : r.placement.cap=cap),
        (panel geo space) hn hh hf hg ht hb ho degreeAt admitted.1 (DateCode.history (codes) boot i) capAt ∧
        (publicOrigins space) hn hh hf hg ht hb ho degreeAt admitted.1 (DateCode.history (codes) boot i) capAt ∧
        (ports).RoleRows ∧ 0<(ports).roleLanes) :
    ∃(geo : Geometry G S b k w i (pos)) (space : support₁) (admitted : ready₁ geo.capacity space),
      (codes) i=issued₁ geo.capacity space ∧ (nextPos).floor=(outer).fullEnd ∧
      (outer).fullEnd<2^w ∧ 8*b.receiverWidth G S k i (ports)≤b.payload ∧
      ∃(hn : n₁=n) (hh : h₁=degree) (hf : f₁=b.f) (hg : g₁=b.gain) (ht : tail₁=b.tail)
        (hb : HEq ctl.board b.board) (ho : RotorSpec.ofRates ctl=b.op) (degreeAt : (ports).venue.degree=D)
        (capAt : r.placement.cap=cap),
        (panel geo space) hn hh hf hg ht hb ho degreeAt admitted.1 (DateCode.history (codes) boot i) capAt ∧
        (publicRows space) hn hh hf hg ht hb ho admitted.1 (DateCode.history (codes) boot i) :=by
  obtain ⟨geo,space,admitted,chosen,nextFloor,roof,short,hn,hh,hf,hg,ht,hb,ho,degreeAt,capAt,panels,rows,_,_⟩ := original
  exact ⟨geo,space,admitted,chosen,nextFloor,roof,short,hn,hh,hf,hg,ht,hb,ho,degreeAt,capAt,panels,
    matched_public_rows_of_origins b.board b.op B b.p b.drift b.degreeLimit b.payload w b.ordinary (pos) space
      hn hh hf hg ht hb ho degreeAt admitted.1 (DateCode.history (codes) boot i) capAt rows⟩


omit [Fintype P] in
private theorem operandPanelsOfIssued (boot : Memory w) (original : ∃(geo : Geometry G S b k w i (pos)) (space : support₁) (admitted : ready₁ geo.capacity space),
      (codes) i=issued₁ geo.capacity space ∧ (nextPos).floor=(outer).fullEnd ∧
      (outer).fullEnd<2^w ∧ 8*b.receiverWidth G S k i (ports)≤b.payload ∧
      ∃(hn : n₁=n) (hh : h₁=degree) (hf : f₁=b.f) (hg : g₁=b.gain) (ht : tail₁=b.tail)
        (hb : HEq ctl.board b.board) (ho : RotorSpec.ofRates ctl=b.op) (degreeAt : (ports).venue.degree=D)
        (capAt : r.placement.cap=cap),
        (panel geo space) hn hh hf hg ht hb ho degreeAt admitted.1 (DateCode.history (codes) boot i) capAt ∧
        (publicRows space) hn hh hf hg ht hb ho admitted.1 (DateCode.history (codes) boot i)) :
    ∃(geo : Geometry G S b k w i (pos)) (space : support₁) (admitted : ready₁ geo.capacity space),
      (codes) i=issued₁ geo.capacity space ∧ (nextPos).floor=(outer).fullEnd ∧
      (outer).fullEnd<2^w ∧ 8*b.receiverWidth G S k i (ports)≤b.payload ∧
      ∃(hn : n₁=n) (hh : h₁=degree) (hf : f₁=b.f) (hg : g₁=b.gain) (ht : tail₁=b.tail)
        (hb : HEq ctl.board b.board) (ho : RotorSpec.ofRates ctl=b.op) (degreeAt : (ports).venue.degree=D)
        (capAt : r.placement.cap=cap),
        (panel geo space) hn hh hf hg ht hb ho degreeAt admitted.1 (DateCode.history (codes) boot i) capAt :=by
  obtain ⟨geo,space,admitted,chosen,nextFloor,roof,short,hn,hh,hf,hg,ht,hb,ho,degreeAt,capAt,panels,_⟩ := original
  exact ⟨geo,space,admitted,chosen,nextFloor,roof,short,hn,hh,hf,hg,ht,hb,ho,degreeAt,capAt,panels⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

/-! # Original archived operand panels on the registered reset execution -/
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
set_option maxHeartbeats 1800000
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

open DescentPackedColony DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks DescentPrimitivePalette
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

local notation "prior₁" => ((cur).ports.afterPad k (cur).floor).archive
local notation "support₁" => PhysicalReset.ScheduledCodeRoom G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports.operandLanes (cur).ports.roleLanes
  (cur).ports.venue (cur).ports.io padEnd w prior₁
local notation "tag₁" => ((kindCalendar S.rounds S.height).drop i).head?
local notation "full₁" => (resetAt i cur).fullEnd
local notation "issued₁" cap₁:arg sp₁:arg => DatePorts.resetDate G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports (cur).floor w cap₁ sp₁
local notation "ready₁" cap₁:arg sp₁:arg => PhysicalReset.ScheduledReady G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports.operandLanes (cur).ports.roleLanes (cur).ports.venue
  (cur).ports.io padEnd w prior₁ cap₁ sp₁
variable {description : BitDescription U} {R : ℕ} (number : Local description)
  (bounds : DatePorts.RangeRoom (cur).ports r description) (shape : WorldShape p R description)
  (label : NodeOrder.All description→Label G s (S.grainAt G.b p 0) op)
  {pointer : NodeOrder.All description→ℕ→Pointer}
  {flags : Fin (2^(cur).ports.venue.k)→Fin (cur).ports.nodes→Fin (cur).ports.operandHosts→Fin (cur).ports.venue.groups→ℕ}
local notation:max "panel" geo:arg sp₁:arg => RegisterTimeline.MatchedRegisteredOperandPanels board op B p drift degree payload w
  (menu).ordinary (menu).seats (menu).profile (menu).header cur sp₁ number bounds shape label geo ((geo).room.archive)
local notation "capacity" => ((capCalendar G.b S.rounds g S.height).take i).prod*256

attribute [local irreducible] traceAt

include before after_ joined in
private theorem namedProfiledRoleRows (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (elapsed : 0 < i) (narrow : 8*(menu).receiverWidth G S k i (cur).ports≤payload) :
    (cur).ports.RoleRows ∧ 0<(cur).ports.roleLanes := by
  let common := all_registered_moves X G S ordinary reset branch positive room shorten w menu rfl rfl rfl
  let suffix := (Path.here.reset B).append after_
  have full : before.append suffix=(traces walk).path :=
    (Path.append_cut_assoc before (Path.here.reset B) after_).symm.trans joined
  have onCut (j : ℕ) (event : RunTrace.Events traces j) : data j :=
    (profiled_installed X G S ordinary reset branch positive room shorten w fit board op frozen
      drift degree payload lo header initial seed₁ placed₁ j event).1
  exact ⟨RegisterTimeline.role_rows_noninitial traces menu initial (fun j a b x y=>common j (cursor j) a b x y)
      placed₁ onCut walk before suffix full elapsed,
    RegisterTimeline.archive_role_prefix traces menu initial (fun j a b x y=>common j (cursor j) a b x y)
      placed₁ onCut walk before suffix full elapsed narrow⟩
include bus seedDegree degreeRoom in
theorem profiled_reset_original_panels (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (incoming : Path.Event.incoming (t:=traces walk) evt cur history) (words : SnapshotWordRoom S n h k tail p f g payload w)
    (previous : DatePorts.ArchiveRead (cur).ports r description number bounds shape op label pointer flags history) :
    ∃(geo : data i) (space : support₁) (admitted : ready₁ geo.capacity space),
      program i=issued₁ geo.capacity space ∧ (cursor (i+1)).floor=full₁ ∧
      full₁<2^w ∧ 8*(menu).receiverWidth G S k i (cur).ports≤payload ∧
      ∃(hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
        (hb : HEq ctl.board board) (ho : RotorSpec.ofRates ctl=op) (degreeAt : (cur).ports.venue.degree=D)
        (capAt : r.placement.cap=capacity),
        (panel geo space) hn hh hf hg ht hb ho degreeAt admitted.1 history capAt ∧
        RegisterTimeline.MatchedPublicOrigins board op B p drift degree payload w (menu).ordinary cur space
          hn hh hf hg ht hb ho degreeAt admitted.1 history capAt ∧
        (cur).ports.RoleRows ∧ 0<(cur).ports.roleLanes :=by
  let ctlFacts := controlsOnProfiledTrace X G S ordinary reset branch positive room shorten walk before B after_ joined
  let recorded := ctlFacts.1
  let operator := ctlFacts.2.1
  let sameTail := ctlFacts.2.2.1
  let elapsed := ctlFacts.2.2.2.1
  let sorted := ctlFacts.2.2.2.2.1
  let grain := ctlFacts.2.2.2.2.2
  let eqs := rotor_control_fields G S ctl reset operator
  let shapeN := eqs.1
  let shapeH := eqs.2.1
  let shapeF := eqs.2.2.2.1
  let shapeG := eqs.2.2.2.2.1
  let degreeD := eqs.2.2.2.2.2.1
  let originalBoard := eqs.2.2.2.2.2.2.2
  let entered := profiled_reset_entry X G S ordinary reset branch positive room shorten w fit board op frozen
      drift degree payload lo header initial bus seedDegree degreeRoom walk m before B after_ joined seed₁ placed₁ incoming
  let geo := entered.choose
  let space := entered.choose_spec.choose
  let entryFacts := entered.choose_spec.choose_spec
  let prepared := entryFacts.1
  let chosen := entryFacts.2.1
  let nextFloor := entryFacts.2.2.1
  let tag := entryFacts.2.2.2.1
  let high := entryFacts.2.2.2.2.1
  let narrow := entryFacts.2.2.2.2.2.1
  let oldCap := entryFacts.2.2.2.2.2.2.2.1
  let census := entryFacts.2.2.2.2.2.2.2.2.1
  let seen := entryFacts.2.2.2.2.2.2.2.2.2
  let roleFacts := namedProfiledRoleRows (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset)
    (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (w:=w) (fit:=fit) (drift:=drift)
    (degree:=degree) (payload:=payload) (lo:=lo) (header:=header) (initial:=initial) (walk:=walk)
    (before:=before) (B:=B) (after_:=after_) (joined:=joined) seed₁ placed₁ elapsed narrow
  let sized := roleFacts.1
  let rolePos := roleFacts.2
  refine RegisterTimeline.calibratedPanelFacts board op B p drift degree payload w
    (menu).ordinary (menu).seats (menu).profile (menu).header cur _ geo shapeG degreeD grain rfl branch
    positive oldCap tag high narrow bus words ?_
  intro atDegree capAt countFit wireAt oldPos oldWidth entryFits low score live degreePos headBits
    hostBits ranks namesFit degFit laneAt hubAt come narrowAt boardAt hostPos newFit
  refine ⟨geo,space,prepared,chosen,nextFloor,high,narrow,shapeN,shapeH,shapeF,shapeG,sameTail,
    originalBoard,operator,atDegree,capAt,?_,?_,sized,rolePos⟩
  · exact RegisterTimeline.matched_operand_panels board op B p drift degree payload w (menu).ordinary (menu).seats
      (menu).profile (menu).header cur («capacity»:=geo.capacity) (space:=space) (number:=number) (bounds:=bounds) (shape:=shape)
      (label:=label) (geo:=geo) («widths»:=geo.room.archive) (paid:=recorded)
      shapeN shapeH shapeF shapeG sameTail originalBoard operator atDegree prepared.1 history incoming grain rfl
      capAt rfl branch seen countFit census wireAt oldPos oldWidth entryFits low score live degreePos headBits
      hostBits ranks namesFit degFit laneAt hubAt come narrowAt bus high boardAt elapsed sorted bounds.positive
      rolePos newFit sized previous
  · exact RegisterTimeline.matched_public_actor_origins board op B p drift degree payload w
      (menu).ordinary (menu).seats (menu).profile (menu).header cur («capacity»:=geo.capacity) (space:=space) (geo:=geo) (paid:=recorded)
      shapeN shapeH shapeF shapeG sameTail originalBoard operator atDegree prepared.1 history grain rfl capAt rfl branch
      seen countFit census wireAt oldPos oldWidth entryFits low score live degreePos headBits hostBits ranks namesFit
      degFit laneAt hubAt come narrowAt bus high boardAt elapsed sorted hostPos
include bus seedDegree degreeRoom in
theorem profiled_reset_issued_panels (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (incoming : Path.Event.incoming (t:=traces walk) evt cur history) (words : SnapshotWordRoom S n h k tail p f g payload w)
    (previous : DatePorts.ArchiveRead (cur).ports r description number bounds shape op label pointer flags history) :
    ∃(geo : data i) (space : support₁) (admitted : ready₁ geo.capacity space),
      program i=issued₁ geo.capacity space ∧ (cursor (i+1)).floor=full₁ ∧
      full₁<2^w ∧ 8*(menu).receiverWidth G S k i (cur).ports≤payload ∧
      ∃(hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
        (hb : HEq ctl.board board) (ho : RotorSpec.ofRates ctl=op) (degreeAt : (cur).ports.venue.degree=D)
        (capAt : r.placement.cap=capacity),
        (panel geo space) hn hh hf hg ht hb ho degreeAt admitted.1 history capAt ∧
        RegisterTimeline.MatchedPublicRows board op B p drift degree payload w (menu).ordinary cur space
          hn hh hf hg ht hb ho admitted.1 history :=by
  exact RegisterTimeline.issuedPanelsOfOriginal traces menu initial i B number bounds shape label m (
    profiled_reset_original_panels X G S ordinary reset branch positive room shorten w fit drift degree payload
      lo header initial bus seedDegree degreeRoom walk m before B after_ joined number bounds shape label
      seed₁ placed₁ incoming words previous)

include bus seedDegree degreeRoom in
theorem profiled_reset_operand_panels (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (incoming : Path.Event.incoming (t:=traces walk) evt cur history) (words : SnapshotWordRoom S n h k tail p f g payload w)
    (previous : DatePorts.ArchiveRead (cur).ports r description number bounds shape op label pointer flags history) :
    ∃(geo : data i) (space : support₁) (admitted : ready₁ geo.capacity space),
      program i=issued₁ geo.capacity space ∧ (cursor (i+1)).floor=full₁ ∧
      full₁<2^w ∧ 8*(menu).receiverWidth G S k i (cur).ports≤payload ∧
      ∃(hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
        (hb : HEq ctl.board board) (ho : RotorSpec.ofRates ctl=op) (degreeAt : (cur).ports.venue.degree=D)
        (capAt : r.placement.cap=capacity),
        (panel geo space) hn hh hf hg ht hb ho degreeAt admitted.1 history capAt :=by
  exact RegisterTimeline.operandPanelsOfIssued traces menu initial i B number bounds shape label m (
    profiled_reset_issued_panels X G S ordinary reset branch positive room shorten w fit drift degree payload
      lo header initial bus seedDegree degreeRoom walk m before B after_ joined number bounds shape label
      seed₁ placed₁ incoming words previous)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

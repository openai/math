import OAI.Hierarchy.DescentMatchedFreshPanelsAt
import OAI.Hierarchy.DescentProfiledResetOperandPanels
import OAI.Hierarchy.DescentMatchedPanelSeven
import OAI.Hierarchy.DescentNamedArchivePrefix
import OAI.Hierarchy.DescentResetPublicationGeometry
import OAI.Hierarchy.DescentResetArchiveCheckpoint
import OAI.Hierarchy.DescentResetArchiveCertificate
import OAI.Hierarchy.DescentPackedCensusInvoice
import OAI.Hierarchy.DescentPrefixArgumentCapacity
import OAI.Hierarchy.DescentNamedPrefixRangeRoom

namespace OAI
/-! # Selected reset operands on the original mathematical archive path -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentSixParty DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentSIMDLookup DescentResetGates
open DescentPackedColony DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks DescentPrimitivePalette
open DescentPackedZip DescentOrdinaryHostPad DescentRetainedRangeDigits
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
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
local notation "oldL" => cursor.ports.operandLanes
local notation "roleL" => cursor.ports.roleLanes
local notation "base" => cursor.ports.priorStart k cursor.floor
local notation "history" => (cursor.ports.afterPad k cursor.floor).archive
local notation "outer" => scheduledAtPorts G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor
local notation "a" => (outer).inner
local notation "v" => (a).successor
local notation "menu" => (⟨board,op,g,tail,p,f,drift,degree,payload,seats,ordinary,profile,header⟩ : Menu n h)
local notation "publisher" => priorArchivePhase G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w
variable (capacity : cursor.ports.venue.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256)
    (space : ScheduledCodeRoom G S board₀ k tail age p f g drift degree payload ordinary op₀
      (S.firstWidth G.b p) (S.grainAt G.b p 0) cursor.ports.operandLanes cursor.ports.roleLanes
      cursor.ports.venue cursor.ports.io (cursor.ports.priorStart k cursor.floor) w (cursor.ports.afterPad k cursor.floor).archive)
local notation "u" => DatePorts.resetInputs G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w space
local notation "ports" => cursor.ports
local notation "mem₁" m:arg => (publisher).image m
variable {description : BitDescription W} {R : ℕ} (number : Local description)
  (bounds : DatePorts.RangeRoom cursor.ports input description) (shape : WorldShape p R description)
  (label : NodeOrder.All description→Label G (S.firstWidth G.b p) (S.grainAt G.b p 0) op₀)

variable (geo : Geometry G S (⟨board₀,op₀,g,tail,p,f,drift,degree,payload,seats,ordinary,profile,header⟩ : Menu n h) k w age cursor)
    (widths : DatePorts.ArchiveWidths G S op₀ cursor.ports k tail p drift degree payload age)
local notation "phase" => (a).ingress.phase base w (io).hubs (fun x=>(io).atoms x.val)
  (fun j=>(io).wire j.1.val j.2.val)
local notation "atMem" m:arg => (phase).image (mem₁ m)

private theorem selectedSevenAtPublicActor (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (hb : HEq ctl.board board₀) (ho : RotorSpec.ofRates ctl=op₀) (degreeAt : (old).degree=D) (ready : (u).Ready)
    (m : Memory w) (capAt : input.placement.cap=cap)
    (held : MatchedRegisteredOperandPanels board₀ op₀ B p drift degree payload w ordinary seats profile header cursor space
      number bounds shape label geo widths hn hh hf hg ht hb ho degreeAt ready m capAt)
    (origins : MatchedPublicOrigins board₀ op₀ B p drift degree payload w ordinary cursor space
      hn hh hf hg ht hb ho degreeAt ready m capAt)
    (small : 2*(v).receiver.candidates<2^(v).receiver.queryBits) :
    MatchedPublicRows board₀ op₀ B p drift degree payload w ordinary cursor space hn hh hf hg ht hb ho ready m ∧
    ∃dst : Memory w, (u).ThroughActors (atMem m) dst ∧
      MatchedPublicOriginsAt board₀ op₀ B p drift degree payload w ordinary cursor space hn hh hf hg ht hb ho degreeAt ready m capAt dst ∧
      MatchedFreshInputsAt board₀ op₀ B p drift degree payload w ordinary cursor space hn hh hf hg ht hb ho ready dst ∧
      ∃read : ∀ix,DatePorts.OrdinalRead (u) ready small dst ix,
        ∀j x nodeSlot laneHost laneGroup,((read ((v).operandOrdinal (u).operand 0 j x nodeSlot)).amount laneHost laneGroup).val≤2 := by
  have published := matched_public_rows_of_origins board₀ op₀ B p drift degree payload w ordinary cursor space hn hh hf hg ht hb ho degreeAt ready m capAt origins
  obtain ⟨dst,run,actor⟩ := origins
  have fresh := matched_fresh_at_public_actor board₀ op₀ B p drift degree payload w ordinary seats profile header cursor space number bounds shape label geo widths hn hh hf hg ht hb ho degreeAt ready m capAt held dst actor
  have words := matched_seven_at_panel board₀ op₀ B p drift degree payload w ordinary seats profile header cursor space number bounds shape label geo widths hn hh hf hg ht hb ho degreeAt ready m capAt held published small dst run
  exact ⟨published,dst,run,actor,fresh.1,words⟩


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

local notation "u₁" space:arg => DatePorts.resetInputs G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload
  b.ordinary b.op s₀ Z₀ (pos).ports (pos).floor w space
local notation "ports₁" space:arg => DatePorts.resetPorts G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload
  b.ordinary b.op s₀ Z₀ (pos).ports (pos).floor w space
local notation "z₁" geo:arg space:arg => DatePorts.resetFinalInputs G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload
  b.ordinary b.op s₀ Z₀ (pos).ports (pos).floor w (geo).capacity space
local notation "pad₁" => priorArchivePhase G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload
  b.ordinary b.op s₀ Z₀ (pos).ports (pos).floor w
local notation "entry₁" => (outer).inner.ingress.phase floor₀ w (ports).io.hubs (fun col=>(ports).io.atoms col.val)
    (fun j=>(ports).io.wire j.1.val j.2.val)
local notation "atMem" boot:arg => (entry₁).image ((pad₁).image (DateCode.history (codes) boot i))

omit [Fintype P] in
private theorem completeSelectedPanels (tags : ∀c,(traces c).path.kinds=kindCalendar S.rounds S.height)
    (kind : e.2.isReset=true) (boot : Memory w) (original : ∃(geo : Geometry G S b k w i (pos)) (space : support₁) (admitted : ready₁ geo.capacity space),
      (codes) i=issued₁ geo.capacity space ∧ (nextPos).floor=(outer).fullEnd ∧
      (outer).fullEnd<2^w ∧ 8*b.receiverWidth G S k i (ports)≤b.payload ∧
      ∃(hn : n₁=n) (hh : h₁=degree) (hf : f₁=b.f) (hg : g₁=b.gain) (ht : tail₁=b.tail)
        (hb : HEq ctl.board b.board) (ho : RotorSpec.ofRates ctl=b.op) (degreeAt : (ports).venue.degree=D)
        (capAt : r.placement.cap=cap),
        (panel geo space) hn hh hf hg ht hb ho degreeAt admitted.1 (DateCode.history (codes) boot i) capAt ∧
        (publicOrigins space) hn hh hf hg ht hb ho degreeAt admitted.1 (DateCode.history (codes) boot i) capAt ∧
        (ports).RoleRows ∧ 0<(ports).roleLanes) :
    ∃(geo : Geometry G S b k w i (pos)) (space : support₁) (admitted : ready₁ geo.capacity space),
      (codes) i=issued₁ geo.capacity space ∧ (nextPos).ports=ports₁ space ∧
      ∃(hn : n₁=n) (hh : h₁=degree) (hf : f₁=b.f) (hg : g₁=b.gain) (ht : tail₁=b.tail)
        (boardAt : HEq ctl.board b.board) (opAt : RotorSpec.ofRates ctl=b.op) (degreeAt : (pos).ports.venue.degree=D)
        (capAt : r.placement.cap=cap),
        RegisterTimeline.MatchedRegisteredOperandPanels (input:=r) (ctl:=ctl) (f:=b.f) (g:=b.gain) (tail:=b.tail) (description:=description) (R:=R) b.board b.op B b.p b.drift b.degreeLimit b.payload w
          b.ordinary b.seats b.profile b.header (pos) space (number) bounds shape
          label geo geo.room.archive hn hh hf hg ht boardAt opAt degreeAt admitted.1 (DateCode.history (codes) boot i) capAt ∧
        RegisterTimeline.MatchedPublicRows b.board b.op B b.p b.drift b.degreeLimit b.payload w b.ordinary (pos) space
          hn hh hf hg ht boardAt opAt admitted.1 (DateCode.history (codes) boot i) ∧
        (pos).ports.RoleRows ∧ 0<(pos).ports.roleLanes ∧
        ∃(layout : DatePorts.ResetPublicationGeometry G S i b.drift (pos).ports (ports₁ space) (u₁ space))
          (actorMem : Memory w), (u₁ space).ThroughActors (atMem boot) actorMem ∧
          RegisterTimeline.MatchedPublicOriginsAt b.board b.op B b.p b.drift b.degreeLimit b.payload w b.ordinary (pos) space
            hn hh hf hg ht boardAt opAt degreeAt admitted.1 (DateCode.history (codes) boot i) capAt actorMem ∧
          RegisterTimeline.MatchedFreshInputsAt b.board b.op B b.p b.drift b.degreeLimit b.payload w b.ordinary (pos) space
            hn hh hf hg ht boardAt opAt admitted.1 actorMem ∧
          (∃read : ∀ix,DatePorts.OrdinalRead (u₁ space) admitted.1 layout.small actorMem ix,
            ∀argIdx blockSlot nodeSlot laneHost laneGroup,((read ((outer).inner.successor.operandOrdinal (u₁ space).operand 0 argIdx blockSlot nodeSlot)).amount laneHost laneGroup).val≤2) ∧
          ∃mid,(u₁ space).throughOperandDate.Runs (atMem boot) mid ∧ (PhysicalReset.date (z₁ geo space)).Runs (atMem boot) (DateCode.history (codes) boot (i+1)) := by
  obtain ⟨geo,space,admitted,chosen,_,roof,_,hn,hh,hf,hg,ht,boardAt,opAt,degAt,capAt,panels,orig,sized,rolePos⟩ := original
  have layout := DatePorts.reset_publication_geometry G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload b.ordinary
    b.op s₀ Z₀ (pos).ports (pos).floor w space geo.format.width
  obtain ⟨portsAt,_,mid,advance,ran⟩ := reset_archive_checkpoint traces b initial i e geo space tags kind roof admitted.1 admitted.2 boot
  obtain ⟨publicRowsAt,actor,physical,origins,fresh,readAt⟩ := selectedSevenAtPublicActor (input:=r) (ctl:=ctl)
    (f:=b.f) (g:=b.gain) (tail:=b.tail) (description:=description) (R:=R)
    b.board b.op B b.p b.drift b.degreeLimit b.payload w b.ordinary b.seats b.profile b.header (pos) space
    number bounds shape label geo geo.room.archive hn hh hf hg ht boardAt opAt degAt admitted.1
    (DateCode.history (codes) boot i) capAt panels orig layout.small
  exact ⟨geo,space,admitted,chosen,portsAt,hn,hh,hf,hg,ht,boardAt,opAt,degAt,capAt,panels,publicRowsAt,sized,rolePos,
    layout,actor,physical,origins,fresh,readAt,mid,advance,ran⟩

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
set_option maxHeartbeats 900000
set_option maxRecDepth 16000
set_option cleanup.letToHave false
local notation "cert" => SeedNamed.normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "trace" => SeedNamed.issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)
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
    (S.firstWidth G.b p) (S.grainAt G.b p 0) a.ports a.floor

local notation "data" => fun i=>Geometry G S menu k w i (cursor i)
local notation "program" => RegisterTimeline.instruction (w:=w) traces menu initial

variable (bus : payload≤w) (seedDegree : initial.ports.venue.degree=3)
    (degreeRoom : maximumDegree (S.rounds+1)+1<2^w)

variable (walk : (last).Choice) (m : Memory w)
variable {U : MarkedWorld F 0 pins widths} {i z D : ℕ}
  {r : Reached U G price fee S k i z D (S.epochPower^S.priceExponent) s}
  {n₁ h₁ C₁ f₁ g₁ cut₁ tail₁ : ℕ} {ctl : ResetRates G S k D n₁ h₁ C₁ f₁ g₁ cut₁ tail₁}
  (before : Path (trace walk).origin.source r) (B : ClosedReset r ctl)
  (after_ : Path B.next (trace walk).target) (joined : (before.reset B).append after_=(trace walk).path)
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

local notation "R₁" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "one₁" => le_max_left 1 (max reset.bitsR (C*reset.bitsR))
private theorem firstWidthGrainDivides (schedule : AtomSchedule) (b divisor : ℕ) :
    divisor ∣ schedule.firstWidth b divisor :=
  Nat.dvd_trans (grainAt_multiple schedule b 0) ⟨b, rfl⟩
local notation "pinWidth" => firstWidthGrainDivides S G.b p
local notation "divides" => fun _ : pins=>by simpa only [Nat.mul_one] using (pinWidth : p∣s)
local notation "source" => (trace walk).origin
open private Origin.archiveShape from OAI.Hierarchy.DescentNamedHistoryShape
open private Origin.archiveOrder from OAI.Hierarchy.DescentNamedPrivateArchive
open private Palette.encodedOrigin from OAI.Hierarchy.DescentNamedPrimitivePalette
local notation "firstShape" => Origin.archiveShape source p R₁ positive one₁ pinWidth
local notation "rawCode" => Palette.encodedOrigin (p:=p) source op reset.menu
local notation "pinNumber" => fun y : pins=>y.1.val
open private chosenClaim from OAI.Hierarchy.DescentNamedArchivePrefix
local notation "claim" => chosenClaim X G S ordinary reset branch positive room shorten w walk
local notation "nextPath" => before.reset B
local notation "oldDesc" hw:arg => (before.archive p positive (source).archive (hw).1).bit
local notation "rank₀" hw:arg => trajectory p positive (source).archive (Origin.archiveOrder source) before (hw).1
local notation "shape₀" hw:arg hb:arg => archiveShape positive one₁ divides (source).archive firstShape before (hw).1 (hb).1
local notation "label₀" hw:arg hr:arg => (encodePath op reset.menu before positive (hw).1 (hr).1 (source).archive rawCode).atNode
local notation "capacity" => ((capCalendar G.b S.rounds g S.height).take i).prod*256
local notation "u₁" sp:arg => DatePorts.resetInputs G S board k frozen i p f g drift degree payload (menu).ordinary op
  s (S.grainAt G.b p 0) (cur).ports (cur).floor w sp
local notation "z₁" geo:arg sp:arg => DatePorts.resetFinalInputs G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports (cur).floor w (geo).capacity sp
local notation "ports₁" sp:arg => DatePorts.resetPorts G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports (cur).floor w sp
local notation "pad₁" => priorArchivePhase G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports (cur).floor w
local notation "ingress" => (inner₁).ingress
local notation "ingressPhase" => (ingress).phase padEnd w (cur).ports.io.hubs (fun x=>(cur).ports.io.atoms x.val)
  (fun j=>(cur).ports.io.wire j.1.val j.2.val)
local notation "atMem" => (ingressPhase).image ((pad₁).image history)
local notation "dst" => DateCode.history program m (i+1)

local notation "ar" pro:arg => before.archive p positive (source).archive pro
local notation "rankOld" pro:arg => trajectory p positive (source).archive (Origin.archiveOrder source) before pro
local notation "schemaOld" pro:arg align:arg => archiveShape positive one₁ divides (source).archive firstShape before pro align
local notation "codeOld" pro:arg only:arg => encodePath op reset.menu before positive pro only (source).archive rawCode
attribute [local irreducible] normalizedPackedChart SeedNamed.issued Origin.source Origin.archivePackage Origin.archiveOrder Origin.archiveShape Palette.encodedOrigin
set_option maxHeartbeats 450000 in
private theorem readPreviousAtPoint (pos : RegisterTimeline.Position) (mem : Memory w)
    (previous : claim before pos mem) (whole : before.whole p) (aligned : before.aligned p R₁) (only : before.OnlyRotor op) :
    ∃ bounds : DatePorts.RangeRoom pos.ports r (ar whole).bit,
      DatePorts.ArchiveRead pos.ports r (ar whole).bit (rankOld whole) bounds (schemaOld whole aligned) op (codeOld whole only).atNode
        (Reached.argumentPointer r (ar whole).bit (rankOld whole) (schemaOld whole aligned) positive pinNumber pos.ports.argumentsPerNode)
        (archiveFlag r (ar whole).bit (rankOld whole) pos.ports bounds) mem := by
  exact previous whole aligned only


include bus seedDegree degreeRoom in
private theorem selectedPanelsOfEarlierRead (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (incoming : Path.Event.incoming (t:=traces walk) evt cur history) (words : SnapshotWordRoom S n h k tail p f g payload w)
    (previous : claim before cur history)
    (hw : (nextPath).whole p) (hb : (nextPath).aligned p R₁) (hr : (nextPath).OnlyRotor op) :
    ∃(bounds : DatePorts.RangeRoom (cur).ports r (oldDesc hw)), ∃(geo : data i) (space : support₁) (admitted : ready₁ geo.capacity space),
      program i=issued₁ geo.capacity space ∧ (cursor (i+1)).floor=full₁ ∧ full₁<2^w ∧
      8*(menu).receiverWidth G S k i (cur).ports≤payload ∧
      ∃(hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
      (boardAt : HEq ctl.board board) (opAt : RotorSpec.ofRates ctl=op) (degreeAt : (cur).ports.venue.degree=D)
      (capAt : r.placement.cap=capacity),
      RegisterTimeline.MatchedRegisteredOperandPanels (F:=F) (P:=pins) (d:=0) (bits:=widths) (W:=U) (G:=G) (q:=price) (ε:=fee) (S:=S) (k:=k) (age:=i) (z:=z) (D:=D) (input:=r) (ctl:=ctl) (n:=n) (h:=h) (f:=f) (g:=g) (tail:=tail) (description:=oldDesc hw) (R:=R₁) board op B p drift degree payload w
       (menu).ordinary (menu).seats (menu).profile (menu).header cur space (rank₀ hw) bounds (shape₀ hw hb)
       (label₀ hw hr) geo geo.room.archive hn hh hf hg ht boardAt opAt degreeAt admitted.1 history capAt ∧
      RegisterTimeline.MatchedPublicOrigins (F:=F) (P:=pins) (d:=0) (bits:=widths) (W:=U) (G:=G) (q:=price) (ε:=fee) (S:=S) (k:=k) (age:=i) (z:=z) (D:=D) (input:=r) (ctl:=ctl) (n:=n) (h:=h) (f:=f) (g:=g) (tail:=tail) board op B p drift degree payload w (menu).ordinary cur space
       hn hh hf hg ht boardAt opAt degreeAt admitted.1 history capAt ∧ (cur).ports.RoleRows ∧ 0<(cur).ports.roleLanes := by
  have readAt := readPreviousAtPoint (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive)
    (room:=room) (shorten:=shorten) (w:=w) (walk:=walk) (before:=before) cur history previous hw.1 hb.1 hr.1
  let bounds := readAt.choose
  have old := readAt.choose_spec
  have selected :=
    profiled_reset_original_panels (F:=F) (cp:=cp) (nP:=nP) (k:=k) (cut:=cut) (tail:=tail) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (r:=r) (ctl:=ctl) (description:=oldDesc hw) (R:=R₁) X G S ordinary reset branch positive room shorten w fit drift degree payload
      lo header initial bus seedDegree degreeRoom walk m before B after_ joined (rank₀ hw) bounds (shape₀ hw hb)
      (label₀ hw hr) seed₁ placed₁ incoming words old
  exact ⟨bounds,selected⟩

open private traceAt_kinds from OAI.Hierarchy.DescentNamedBranchMachine
include bus seedDegree degreeRoom in
/-- The same real old archive funds the registered operand choice and the native return. -/
theorem profiled_reset_seven_origins (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (incoming : Path.Event.incoming (t:=traces walk) evt cur history) (words : SnapshotWordRoom S n h k tail p f g payload w)
    (previous : claim before cur history) :
    ∃(hw : (nextPath).whole p) (hb : (nextPath).aligned p R₁) (hr : (nextPath).OnlyRotor op)
      (bounds : DatePorts.RangeRoom (cur).ports r (oldDesc hw))
      (geo : data i) (space : support₁) (admitted : ready₁ geo.capacity space),
      program i=issued₁ geo.capacity space ∧ (cursor (i+1)).ports=ports₁ space ∧
      ∃(hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
        (boardAt : HEq ctl.board board) (opAt : RotorSpec.ofRates ctl=op) (degreeAt : (cur).ports.venue.degree=D)
        (capAt : r.placement.cap=capacity),
        RegisterTimeline.MatchedRegisteredOperandPanels (input:=r) (ctl:=ctl) (f:=f) (g:=g) (tail:=tail) (description:=oldDesc hw) (R:=R₁) board op B p drift degree payload w
          (menu).ordinary (menu).seats (menu).profile (menu).header cur space (rank₀ hw) bounds (shape₀ hw hb)
          (label₀ hw hr) geo geo.room.archive hn hh hf hg ht boardAt opAt degreeAt admitted.1 history capAt ∧
        RegisterTimeline.MatchedPublicRows board op B p drift degree payload w (menu).ordinary cur space
          hn hh hf hg ht boardAt opAt admitted.1 history ∧
        (cur).ports.RoleRows ∧ 0<(cur).ports.roleLanes ∧
        ∃(layout : DatePorts.ResetPublicationGeometry G S i drift (cur).ports (ports₁ space) (u₁ space))
          (actorMem : Memory w), (u₁ space).ThroughActors atMem actorMem ∧
          RegisterTimeline.MatchedPublicOriginsAt board op B p drift degree payload w (menu).ordinary cur space
            hn hh hf hg ht boardAt opAt degreeAt admitted.1 history capAt actorMem ∧
          RegisterTimeline.MatchedFreshInputsAt board op B p drift degree payload w (menu).ordinary cur space
            hn hh hf hg ht boardAt opAt admitted.1 actorMem ∧
          (∃read : ∀ix,DatePorts.OrdinalRead (u₁ space) admitted.1 layout.small actorMem ix,
            ∀argIdx blockSlot nodeSlot laneHost laneGroup,((read ((inner₁).successor.operandOrdinal (u₁ space).operand 0 argIdx blockSlot nodeSlot)).amount laneHost laneGroup).val≤2) ∧
          ∃mid,(u₁ space).throughOperandDate.Runs atMem mid ∧ (PhysicalReset.date (z₁ geo space)).Runs atMem dst :=by
  have witnesses := prefix_archive_witnesses (F:=F) (cp:=cp) (nP:=nP) (k:=k) (cut:=cut) (tail:=tail) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p)
    X G S ordinary reset branch positive room shorten walk nextPath after_ joined
  have hw := witnesses.1
  have hb := witnesses.2.1
  have hr := witnesses.2.2
  have earlier := selectedPanelsOfEarlierRead (F:=F) (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch)
    (positive:=positive) (room:=room) (shorten:=shorten) (w:=w) (fit:=fit) (drift:=drift) (degree:=degree)
    (payload:=payload) (lo:=lo) (header:=header) (initial:=initial) (bus:=bus) (seedDegree:=seedDegree)
    (degreeRoom:=degreeRoom) (walk:=walk) (m:=m) (before:=before) (B:=B) (after_:=after_) (joined:=joined)
    seed₁ placed₁ incoming words previous hw hb hr
  let bounds := earlier.choose
  have selected := earlier.choose_spec
  have tailFacts := RegisterTimeline.completeSelectedPanels
    (F:=F) (P:=pins) (G:=G) (S:=S) (bits:=widths) (d:=0) (k:=k) (wire:=S.epochPower^S.priceExponent) (hist:=s)
    (final:=S.length) (w:=w) (q:=price) (ε:=fee) (C:=(last).Choice) (n:=n) (degree:=h) (U:=U) (z:=z) (D:=D)
    (n₁:=n₁) (h₁:=h₁) (C₁:=C₁) (f₁:=f₁) (g₁:=g₁) (cut₁:=cut₁) (tail₁:=tail₁) (r:=r) (ctl:=ctl)
    (description:=oldDesc hw) (R:=R₁) traces menu initial i ⟨walk,evt⟩ B
    (rank₀ hw) bounds (shape₀ hw hb) (label₀ hw hr) (traceAt_kinds X G S ordinary reset branch positive room shorten) rfl m selected
  first | with_reducible exact ⟨hw,hb,hr,bounds,tailFacts⟩ | exact ⟨hw,hb,hr,bounds,tailFacts⟩


include bus seedDegree degreeRoom in
/-- The same real old archive funds the registered operand choice and the native return. -/
theorem profiled_reset_seven_source (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (incoming : Path.Event.incoming (t:=traces walk) evt cur history) (words : SnapshotWordRoom S n h k tail p f g payload w)
    (previous : claim before cur history) :
    ∃(hw : (nextPath).whole p) (hb : (nextPath).aligned p R₁) (hr : (nextPath).OnlyRotor op)
      (bounds : DatePorts.RangeRoom (cur).ports r (oldDesc hw))
      (geo : data i) (space : support₁) (admitted : ready₁ geo.capacity space),
      program i=issued₁ geo.capacity space ∧ (cursor (i+1)).ports=ports₁ space ∧
      ∃(hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
        (boardAt : HEq ctl.board board) (opAt : RotorSpec.ofRates ctl=op) (degreeAt : (cur).ports.venue.degree=D)
        (capAt : r.placement.cap=capacity),
        RegisterTimeline.MatchedRegisteredOperandPanels board op B p drift degree payload w
          (menu).ordinary (menu).seats (menu).profile (menu).header cur space (rank₀ hw) bounds (shape₀ hw hb)
          (label₀ hw hr) geo geo.room.archive hn hh hf hg ht boardAt opAt degreeAt admitted.1 history capAt ∧
        RegisterTimeline.MatchedPublicRows board op B p drift degree payload w (menu).ordinary cur space
          hn hh hf hg ht boardAt opAt admitted.1 history ∧
        ∃(layout : DatePorts.ResetPublicationGeometry G S i drift (cur).ports (ports₁ space) (u₁ space))
          (actorMem : Memory w), (u₁ space).ThroughActors atMem actorMem ∧
          (∃read : ∀ix,DatePorts.OrdinalRead (u₁ space) admitted.1 layout.small actorMem ix,
            ∀j x nodeSlot h₀ g₀,((read ((inner₁).successor.operandOrdinal (u₁ space).operand 0 j x nodeSlot)).amount h₀ g₀).val≤2) ∧
          ∃mid,(u₁ space).throughOperandDate.Runs atMem mid ∧ (PhysicalReset.date (z₁ geo space)).Runs atMem dst :=by
  have selected :=
    profiled_reset_seven_origins X G S ordinary reset branch positive room shorten w fit drift degree payload
      lo header initial bus seedDegree degreeRoom walk m before B after_ joined seed₁ placed₁ incoming words previous
  refine Exists.imp (fun _ stage => ?_) selected
  iterate 6 refine Exists.imp (fun _ stage => ?_) stage
  refine ⟨stage.1, stage.2.1, ?_⟩
  refine Exists.imp (fun _ calibration => ?_) stage.2.2
  iterate 8 refine Exists.imp (fun _ calibration => ?_) calibration
  refine ⟨calibration.1, calibration.2.1, ?_⟩
  refine Exists.imp (fun _ layout => ?_) calibration.2.2.2.2
  refine Exists.imp (fun _ actor => ?_) layout
  exact ⟨actor.1, actor.2.2.2⟩

include after_ joined in
/-- Previous logical recipes have exactly the paid and exterior atoms on the chosen path. -/
theorem profiled_reset_tokens (hw : (nextPath).whole p) :
    (oldDesc hw).Tokenized r.placement.records :=by
  let suffix := (Path.here.reset B).append after_
  have path : before.append suffix=(trace walk).path :=
    (Path.append_cut_assoc before (Path.here.reset B) after_).symm.trans joined
  exact Branch.prefix_tokenized X G S (trace walk) positive before suffix path hw.1

include before after_ joined in
theorem profiled_reset_paid_precision (geo : data i) (space : support₁)
    (layout : DatePorts.ResetPublicationGeometry G S i drift (cur).ports (ports₁ space) (u₁ space)) :
    B.next.placement.wire*(B.next.placement.z*G.b)*B.next.placement.cap <
      2^(inner₁).successor.metadata.paidBits :=by
  obtain ⟨_,_,_,_,_,grain⟩:=profiled_reset_controls X G S ordinary reset branch positive room shorten
    walk before B after_ joined
  rw [layout.paidBits,geo.format.paid]
  exact (B.next.placement.census_caps_at S B.next.valid ctl.height B.age
    (B.next.grain.trans grain) B.next.edges branch).2

include after_ joined in
theorem profiled_reset_next_room (geo : data i) (space : support₁)
    (layout : DatePorts.ResetPublicationGeometry G S i drift (cur).ports (ports₁ space) (u₁ space))
    (hw : (nextPath).whole p) :
    DatePorts.RangeRoom (ports₁ space) B.next ((nextPath).archive p positive (source).archive hw).bit :=by
  refine ⟨?_,?_,layout.groups.symm,(layout.radix.trans geo.format.width).symm,layout.positiveLanes⟩
  · intro v
    have held := Branch.prefix_nodes X G S (trace walk) positive ctl.height nextPath after_ joined hw v
    exact Nat.le_trans held (Nat.le_of_eq layout.nodeCount.symm)
  · intro v
    have held := (B.next.vertex (B.next.placement.pos v).2).isLt.trans_le B.next.valid.host
    exact Nat.lt_of_lt_of_le held (Nat.le_of_eq layout.hosts.symm)

theorem profiled_reset_argument_room (space : support₁)
    (layout : DatePorts.ResetPublicationGeometry G S i drift (cur).ports (ports₁ space) (u₁ space))
    (limit : R₁≤drift) (hw : (nextPath).whole p)
    (shape : WorldShape p R₁ ((nextPath).archive p positive (source).archive hw).bit)
    (y : NodeOrder.All ((nextPath).archive p positive (source).archive hw).bit) :
    (DescentRetainedRangeDigits.occurrences (shape.sites y.1) y.2).length≤(u₁ space).operand.slots :=by
  have held := Branch.prefix_argument_capacity X G S (trace walk) positive nextPath hw ctl.height branch shape y.1 y.2
  have wider : S.retainedArgumentsAt G R₁ ≤ S.retainedArgumentsAt G drift :=
    Nat.mul_le_mul_right _ (Nat.add_le_add_right limit 1)
  exact held.trans (wider.trans (Nat.le_of_eq (layout.operandSlots.trans layout.slots).symm))

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

import OAI.Hierarchy.DescentProfiledResetOperandPanels
import OAI.Hierarchy.DescentMatchedPanelTags
import OAI.Hierarchy.DescentNamedResetArchiveTags

namespace OAI
/-! # All actual tagged operand pages on the registered successor memory -/
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

set_option maxHeartbeats 650000
omit [Fintype P] in
/-- The selected reset publishes the panel tags read on its own actor execution. -/
private theorem tag_sources_on_registered_panels (boot : Memory w) (hi : i≤final)
    (tags : ∀c,(traces c).path.kinds=kindCalendar S.rounds S.height)
    (kind : e.2.isReset=true) (bus : b.payload≤w) (degreeRoom : (ports).venue.degree+1<2^w)
    (panelReads : ∃(geo : Geometry G S b k w i (pos)) (space : support₁) (admitted : ready₁ geo.capacity space),
      (codes) i=issued₁ geo.capacity space ∧ (nextPos).floor=(outer).fullEnd ∧
      (outer).fullEnd<2^w ∧ 8*b.receiverWidth G S k i (ports)≤b.payload ∧
      ∃(hn : n₁=n) (hh : h₁=degree) (hf : f₁=b.f) (hg : g₁=b.gain) (ht : tail₁=b.tail)
        (hb : HEq ctl.board b.board) (ho : RotorSpec.ofRates ctl=b.op) (degreeAt : (ports).venue.degree=D)
        (capAt : r.placement.cap=cap),
        (panel geo space) hn hh hf hg ht hb ho degreeAt admitted.1 (DateCode.history (codes) boot i) capAt ∧
        (publicRows space) hn hh hf hg ht hb ho admitted.1 (DateCode.history (codes) boot i)) :
    ResetTagSources traces b initial i e boot :=by
  obtain ⟨geo,space,admitted,_,_,roof,short,hn,hh,hf,hg,ht,hb,ho,degreeAt,capAt,panels,held⟩ := panelReads
  have small : 2*(receiver).candidates<2^(receiver).queryBits :=
    (Nat.lt_succ_self _).trans_le (Nat.le_pow_clog (by decide : 1<2) _)
  have observed := matched_panel_tags b.board b.op B b.p b.drift b.degreeLimit b.payload w b.ordinary
    b.seats b.profile b.header (pos) space number bounds shape label geo geo.room.archive
    hn hh hf hg ht hb ho degreeAt admitted.1 (DateCode.history (codes) boot i) capAt panels held small
  refine ⟨geo,space,tags,kind,short,bus,degreeRoom,roof,?_⟩
  rw [history_from_cuts traces b initial e.1 boot i hi]
  exact observed

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
local notation "data" => fun i=>Geometry G S menu k w i (cursor i)
local notation "program" => RegisterTimeline.instruction (w:=w) traces menu initial

variable (bus : payload≤w) (seedDegree : initial.ports.venue.degree=3)
    (degreeRoom : maximumDegree (S.rounds+1)+1<2^w)

attribute [local irreducible] normalizedPackedChart SeedNamed.issued Origin.source Origin.archivePackage
variable (walk : (last).Choice) (m : Memory w)
variable {U : MarkedWorld F 0 pins widths} {i z D : ℕ}
  {r : Reached U G price fee S k i z D (S.epochPower^S.priceExponent) s}
  {n₁ h₁ C₁ f₁ g₁ cut₁ tail₁ : ℕ} {ctl : ResetRates G S k D n₁ h₁ C₁ f₁ g₁ cut₁ tail₁}
  (before : Path (traces walk).first r) (B : ClosedReset r ctl)
  (after_ : Path B.next (traces walk).last) (joined : (before.reset B).append after_=(traces walk).path)
local notation "evt" => (Path.Event.reset before B after_ joined : (traces walk).path.Event i)
local notation "cur" => cursor i
local notation "history" => DateCode.history program m i
variable {description : BitDescription U} {R : ℕ} (number : Local description)
  (bounds : DatePorts.RangeRoom (cur).ports r description) (shape : WorldShape p R description)
  (label : NodeOrder.All description→Label G s (S.grainAt G.b p 0) op)
  {pointer : NodeOrder.All description→ℕ→Pointer}
  {flags : Fin (2^(cur).ports.venue.k)→Fin (cur).ports.nodes→Fin (cur).ports.operandHosts→Fin (cur).ports.venue.groups→ℕ}
local notation "tagSources" => RegisterTimeline.ResetTagSources traces menu initial i ⟨walk,evt⟩ m
local notation "cpu" => RunTrace.machine traces (fun t _=>program t)
private theorem actualResetKinds (choice : (last).Choice) :
    (traces choice).path.kinds=kindCalendar S.rounds S.height := by
  dsimp only [traceAt]
  exact (trace choice).kinds

attribute [local irreducible] traceAt
include X G S ordinary reset branch positive room shorten w fit drift degree payload lo header initial bus seedDegree degreeRoom walk m before B after_ joined in
theorem profiled_reset_tag_sources (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (incoming : Path.Event.incoming (t:=traces walk) evt cur history) (words : SnapshotWordRoom S n h k tail p f g payload w)
    (previous : DatePorts.ArchiveRead (cur).ports r description number bounds shape op label pointer flags history) : tagSources :=by
  have schedule := actualResetKinds X G S ordinary reset branch positive room shorten
  apply RegisterTimeline.tag_sources_on_registered_panels traces menu initial i ⟨walk,evt⟩ B number bounds shape label m B.age.le
    schedule rfl bus (RegisterTimeline.calendar_degree_room traces menu schedule initial seedDegree degreeRoom i)
  exact profiled_reset_issued_panels X G S ordinary reset branch positive room shorten w fit drift degree payload
    lo header initial bus seedDegree degreeRoom walk m before B after_ joined number bounds shape label
    seed₁ placed₁ incoming words previous

include X G S ordinary reset branch positive room shorten w fit drift degree payload lo header initial bus seedDegree degreeRoom walk m before B after_ joined in
theorem profiled_reset_archive_tags (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (incoming : Path.Event.incoming (t:=traces walk) evt cur history) (words : SnapshotWordRoom S n h k tail p f g payload w)
    (previous : DatePorts.ArchiveRead (cur).ports r description number bounds shape op label pointer flags history) :
    DatePorts.ArchiveTags (cursor (i+1)).ports (DateCode.history cpu m (i+1)) :=
  (profiled_reset_tag_sources X G S ordinary reset branch positive room shorten w fit drift degree payload
    lo header initial bus seedDegree degreeRoom walk m before B after_ joined number bounds shape label
    seed₁ placed₁ incoming words previous).result

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

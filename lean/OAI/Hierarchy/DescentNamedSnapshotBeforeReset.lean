import OAI.Hierarchy.DescentNamedProfiledAdmission
import OAI.Hierarchy.DescentRegisteredSnapshotInput
import OAI.Hierarchy.DescentNamedPrefixState
import OAI.Hierarchy.DescentFixedResetGeometry

namespace OAI
open private source_cap from OAI.Hierarchy.DescentNamedOrdinaryCode

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open scoped Fin.CommRing
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option cleanup.letToHave false
set_option quotPrecheck false
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentPacking.PackedMatch.Local.Stage
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
  {n h k w wire hist len d : ℕ} {q ε : ℝ} {bits : P → ℕ} {T : Type*}
  (ts : T → RunTrace G q ε S k wire hist len bits d) (b₀ : RegisterTimeline.Menu n h)
  (initial : RegisterTimeline.Position) (walk : T) {U : MarkedWorld F d P bits} {i z D : ℕ}
  {r : Reached U G q ε S k i z D wire hist}
  {n₁ h₁ C₁ f₁ g₁ cut₁ tail₁ : ℕ} {ctl : ResetRates G S k D n₁ h₁ C₁ f₁ g₁ cut₁ tail₁}
  (before : Path (ts walk).first r) (B : ClosedReset r ctl) (after_ : Path B.next (ts walk).last)
  (joined : (before.reset B).append after_=(ts walk).path)
  (tagsMatch : ∀x,(ts x).path.kinds = kindCalendar S.rounds S.height)
  (capMatch : (ts walk).path.capFactors = capCalendar G.b S.rounds b₀.gain S.height)
  (sourceCap : (ts walk).first.placement.cap = 256)
  (bus : b₀.payload ≤ w) (seedDegree : initial.ports.venue.degree=3)
  (degreeRoom : maximumDegree (S.rounds+1)+1<2^w) (ram₀ : Memory w)
local notation "evt" => (Path.Event.reset before B after_ joined : (ts walk).path.Event i)
local notation "cursor" => RegisterTimeline.calendar (w:=w) ts b₀ initial
local notation "cur" => cursor i
local notation "data" j:arg => Geometry G S b₀ k w j (cursor j)
local notation "program" => RegisterTimeline.instruction (w:=w) ts b₀ initial
local notation "s" => S.firstWidth G.b b₀.p
local notation "capSeq" => capCalendar G.b S.rounds b₀.gain S.height
local notation "resetAt" j:arg u:arg => PhysicalReset.scheduledAtPorts G S b₀.board k b₀.tail j b₀.p b₀.f b₀.gain b₀.drift b₀.degreeLimit b₀.payload b₀.ordinary b₀.op s (S.grainAt G.b b₀.p 0) (u).ports (u).floor
local notation "pub" => priorArchivePhase G S b₀.board k b₀.tail i b₀.p b₀.f b₀.gain b₀.drift b₀.degreeLimit b₀.payload (b₀).ordinary b₀.op s
    (S.grainAt G.b b₀.p 0) (cur).ports (cur).floor w
local notation "padEnd" => (cur).ports.priorStart k (cur).floor


local notation "prior₁" => ((cur).ports.afterPad k (cur).floor).archive
local notation "support₁" => PhysicalReset.ScheduledCodeRoom G S b₀.board k b₀.tail i b₀.p b₀.f b₀.gain b₀.drift b₀.degreeLimit b₀.payload
  (b₀).ordinary b₀.op s (S.grainAt G.b b₀.p 0) (cur).ports.operandLanes (cur).ports.roleLanes
  (cur).ports.venue (cur).ports.io padEnd w prior₁
local notation "padded₁" => (pub).image ram₀
local notation "tag₁" => ((kindCalendar S.rounds S.height).drop i).head?
local notation "full₁" => (resetAt i cur).fullEnd
local notation "issued₁" cap₁:arg sp₁:arg => DatePorts.resetDate G S b₀.board k b₀.tail i b₀.p b₀.f b₀.gain b₀.drift b₀.degreeLimit b₀.payload
  (b₀).ordinary b₀.op s (S.grainAt G.b b₀.p 0) (cur).ports (cur).floor w cap₁ sp₁
local notation "ready₁" cap₁:arg sp₁:arg => PhysicalReset.ScheduledReady G S b₀.board k b₀.tail i b₀.p b₀.f b₀.gain b₀.drift b₀.degreeLimit b₀.payload
  (b₀).ordinary b₀.op s (S.grainAt G.b b₀.p 0) (cur).ports.operandLanes (cur).ports.roleLanes (cur).ports.venue
  (cur).ports.io padEnd w prior₁ cap₁ sp₁
include capMatch sourceCap in
omit [Fintype P] in
private theorem registeredSnapshotOnReset (geo : data i)
    (previous : (cur).ports.held r (cur).floor ram₀) (mv : Move w)
    (posted : RegisterTimeline.issued ts b₀ i ⟨walk,evt⟩ cur mv)
    (top : mv.next.floor<2^w) :
    (pub).Runs ram₀ ∧ (cur).ports.venue.cap=r.placement.cap ∧
    padded₁ (cur).ports.archive.count.base=(Fintype.card r.V:Computability.VPVNP.BurstRAM.Word w) ∧
    stageVenue r r.valid.host (cur).ports.io (cur).ports.venue.lanes (cur).ports.venue.paidBits padEnd
      (r.venueRoster r.valid.host) padded₁ := by
  let suffix := (Path.here.reset B).append after_
  have full : before.append suffix=(ts walk).path :=
    (Path.append_cut_assoc before (Path.here.reset B) after_).symm.trans joined
  have priced := before.capacity_prefix suffix capSeq ((congrArg Path.capFactors full).trans capMatch)
  simp only [Nat.sub_zero,sourceCap] at priced
  have eqCap := geo.capacity.trans priced.symm
  have roof : full₁<2^w := by obtain ⟨cf,sp,rfl⟩:=posted; exact top
  obtain ⟨padded,wide,seen,counted⟩ := RegisterTimeline.snapshot_padded_held b₀ cur r geo eqCap roof ram₀ previous
  refine ⟨padded,eqCap,counted,?_⟩
  have normalize (N : ℕ) (bound : Fintype.card r.V≤N) (e : N=S.hostSize i)
      (v : stageVenue r bound (cur).ports.io (cur).ports.venue.lanes (cur).ports.venue.paidBits padEnd (r.venueRoster bound) padded₁) :
      stageVenue r r.valid.host (cur).ports.io (cur).ports.venue.lanes (cur).ports.venue.paidBits padEnd (r.venueRoster r.valid.host) padded₁ := by
    subst N
    exact v
  exact normalize _ wide geo.room.hosts seen
end
end Hierarchy.DescentSixParty.SeedNamed

/-! # Read the previous signed graph and its size before every selected actor census -/
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
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option cleanup.letToHave false
open scoped Fin.CommRing
attribute [local irreducible] normalizedPackedChart SeedNamed.issued Origin.source Origin.archivePackage
local notation "cert" => SeedNamed.normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => SeedNamed.issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : s < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentPacking.PackedMatch.Local.Stage
variable {n₀ δ : ℕ} (board : NonlinearExpanders.Graph n₀ δ) (op : RotorSpec)
    (frozen drift degree payload lo header : ℕ) (initial : RegisterTimeline.Position)
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial
local notation "model" i:arg a:arg tick:arg =>
  DatePorts.ordinaryModel (a:RegisterTimeline.Position).ports tick op g frozen p f drift degree payload ((menu).seats i) a.floor (menu).ordinary
local notation "resetAt" => fun i (a:RegisterTimeline.Position)=>
  PhysicalReset.scheduledAtPorts G S board k frozen i p f g drift degree payload (menu).ordinary op
    (S.firstWidth G.b p) (S.grainAt G.b p 0) (a).ports (a).floor

local notation "numbers" => profiledNumbers X G S ordinary reset branch positive room shorten w fit
  board op frozen drift degree payload lo header initial
local notation:max "data" j:arg => Geometry G S menu k w j (cursor j)
local notation "issue" => RegisterTimeline.issued (w:=w) traces menu
local notation "program" => RegisterTimeline.instruction (w:=w) traces menu initial

variable (bus : payload≤w) (site : 0<k) (seedDegree : initial.ports.venue.degree=3)
    (degreeRoom : maximumDegree (S.rounds+1)+1<2^w) (seed : data 0)
    (paid : ∀i,∀e:RunTrace.Events traces i,data i→numbers i e)



variable (bits₀ : (ch).Pin→Bool) (walk : (last).Choice) (m : Memory w)
local notation "limit" => ((ch).rows bits₀).length
local notation "valid" => (ch).read bits₀=some walk
local notation "capSeq" => capCalendar G.b S.rounds g S.height
variable (selected : valid)
  (boot : initial.ports.held (trace walk).origin.source initial.floor m)
  (advances_ : ∀i (e : (traces walk).path.Event i),data i →
    RegisterTimeline.advances traces menu initial walk m limit valid i e)
  {U : MarkedWorld F 0 pins widths} {i z D : ℕ}
  {r : Reached U G price fee S k i z D (S.epochPower^S.priceExponent) s}
  {n₁ h₁ C₁ f₁ g₁ cut₁ tail₁ : ℕ} {ctl : ResetRates G S k D n₁ h₁ C₁ f₁ g₁ cut₁ tail₁}
  (before : Path (traces walk).first r) (B : ClosedReset r ctl)
  (after_ : Path B.next (traces walk).last) (joined : (before.reset B).append after_=(traces walk).path)
local notation "evt" => (Path.Event.reset before B after_ joined : (traces walk).path.Event i)
local notation "cur" => cursor i
local notation "history" => DateCode.history program m i
local notation "pub" => priorArchivePhase G S board k frozen i p f g drift degree payload (menu).ordinary op s
    (S.grainAt G.b p 0) (cur).ports (cur).floor w
local notation "padEnd" => (cur).ports.priorStart k (cur).floor

include selected boot advances_ bus site seedDegree degreeRoom seed paid in
theorem profiled_snapshot_before_reset (move : Move w) (at_ : issue i ⟨walk,evt⟩ cur move)
    (space : move.next.floor<2^w) :
    (pub).Runs history ∧ (cur).ports.venue.cap = r.placement.cap ∧
    (pub).image history (cur).ports.archive.count.base=(Fintype.card r.V:Computability.VPVNP.BurstRAM.Word w) ∧
    stageVenue r r.valid.host (cur).ports.io (cur).ports.venue.lanes (cur).ports.venue.paidBits padEnd
      (r.venueRoster r.valid.host) ((pub).image history) := by
  let suffix:=(Path.here.reset B).append after_
  have cut₀ : before.append suffix=(trace walk).path:=
    (Path.append_cut_assoc before (Path.here.reset B) after_).symm.trans joined
  have placed:=profiled_placement X G S ordinary reset branch positive room shorten w fit board op frozen drift
    degree payload lo header initial bus site seedDegree degreeRoom
  obtain ⟨geo,previous,_⟩:=original_prefix_state X G S ordinary reset branch positive room shorten w fit menu
    initial rfl rfl rfl seed (fun j e=>placed j e (paid j e)) bits₀ walk m boot advances_ before suffix cut₀
    (Or.inr selected)
  rw [←RegisterTimeline.position_floor issue initial i] at previous
  have sourceCap : (traces walk).first.placement.cap=256 := by
    let origin := (trace walk).origin
    exact source_cap origin
  have gainEq : (menu).gain=g := rfl
  have capMatch : (traces walk).path.capFactors = capCalendar G.b S.rounds (menu).gain S.height := by
    rw [gainEq]
    exact (trace walk).calendar
  exact registeredSnapshotOnReset (ts:=traces) (b₀:=menu) (initial:=initial) (walk:=walk)
    (before:=before) (B:=B) (after_:=after_) (joined:=joined) (capMatch:=capMatch)
    (sourceCap:=sourceCap) (ram₀:=history) geo previous move at_ space

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

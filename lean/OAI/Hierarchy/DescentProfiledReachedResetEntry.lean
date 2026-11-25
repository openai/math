import OAI.Hierarchy.DescentNamedSnapshotBeforeReset
import OAI.Hierarchy.DescentRegisteredSelectedReady
import OAI.Hierarchy.DescentNamedProfiledNumbers

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
private abbrev registeredResetEntryResult :=
    ∃(geo : data i) (space : support₁),
      ready₁ geo.capacity space ∧ program i=issued₁ geo.capacity space ∧ (cursor (i+1)).floor=full₁ ∧
      tag₁=some true ∧ full₁<2^w ∧ 8*(b₀).receiverWidth G S k i (cur).ports≤b₀.payload ∧
      (pub).Runs ram₀ ∧ (cur).ports.venue.cap=r.placement.cap ∧
      padded₁ (cur).ports.archive.count.base=(Fintype.card r.V:Computability.VPVNP.BurstRAM.Word w) ∧
      stageVenue r r.valid.host (cur).ports.io (cur).ports.venue.lanes (cur).ports.venue.paidBits padEnd
        (r.venueRoster r.valid.host) padded₁

include tagsMatch capMatch sourceCap bus seedDegree degreeRoom in
omit [Fintype P] in
private theorem registeredResetEntryAt
    (installed : data i ∧ ∃mv : Move w, RegisterTimeline.issued ts b₀ i ⟨walk,evt⟩ cur mv ∧ mv.next.floor<2^w ∧
       ((evt).isReset=true → 8*b₀.receiverWidth G S k i (cur).ports≤b₀.payload))
    (incoming₀ : (cur).ports.held r (cur).floor ram₀) :
    registeredResetEntryResult ts b₀ initial (r:=r) ram₀ :=by
  let ev : RunTrace.Events ts i:=⟨walk,evt⟩
  obtain ⟨geo,mv,which,top,short⟩:=installed
  obtain ⟨cap₁,space,rfl⟩:=which
  have deg:=RegisterTimeline.calendar_degree_room ts b₀ tagsMatch initial seedDegree degreeRoom i
  have ready:=RegisterTimeline.reset_issued_ready ts b₀ initial tagsMatch i ev rfl geo
    (short rfl) bus deg top space
  have tag : tag₁=some true := by
    rw [← tagsMatch walk]
    exact (evt).shown.trans (congrArg some (show (evt).isReset=true from rfl))
  have chosen:=RegisterTimeline.reset_return ts b₀ initial i ev rfl geo.capacity space (fun b=>by
    have l:=b.2.shown
    rw [tagsMatch b.1,tag] at l
    exact (Option.some.inj l).symm)
  let suffix:=(Path.here.reset B).append after_
  have cut₀ : before.append suffix=(ts walk).path :=
    (Path.append_cut_assoc before (Path.here.reset B) after_).symm.trans joined
  have capPrefix:=before.capacity_prefix suffix capSeq ((congrArg Path.capFactors cut₀).trans capMatch)
  simp only [Nat.sub_zero,sourceCap] at capPrefix
  have sameCap : (cur).ports.venue.cap=r.placement.cap :=geo.capacity.trans capPrefix.symm
  obtain ⟨pad_,wide,seen,counted⟩:=RegisterTimeline.snapshot_padded_held b₀ cur r geo sameCap top ram₀ incoming₀
  refine ⟨geo,space,ready,chosen.1,congrArg Position.floor chosen.2.1,tag,top,short rfl,pad_,sameCap,counted,?_⟩
  have castHost (N : ℕ) (available : Fintype.card r.V≤N) (eqn : N=S.hostSize i)
      (read : stageVenue r available (cur).ports.io (cur).ports.venue.lanes (cur).ports.venue.paidBits padEnd
        (r.venueRoster available) padded₁) :
      stageVenue r r.valid.host (cur).ports.io (cur).ports.venue.lanes (cur).ports.venue.paidBits padEnd
        (r.venueRoster r.valid.host) padded₁ :=by subst N;exact read
  exact castHost _ wide geo.room.hosts seen

end
end Hierarchy.DescentSixParty.SeedNamed

/-! # The prior state and selected native program for a profiled reset event -/
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
set_option maxHeartbeats 1600000
set_option cleanup.letToHave false
attribute [local irreducible] normalizedPackedChart SeedNamed.issued Origin.source Origin.archivePackage
open scoped Fin.CommRing
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

local notation:max "data" j:arg => Geometry G S menu k w j (cursor j)
local notation "issue" => RegisterTimeline.issued (w:=w) traces menu
local notation "program" => RegisterTimeline.instruction (w:=w) traces menu initial

variable (bus : payload≤w) (seedDegree : initial.ports.venue.degree=3) (degreeRoom : maximumDegree (S.rounds+1)+1<2^w)
variable (walk : (last).Choice) (m : Memory w)
local notation "capSeq" => capCalendar G.b S.rounds g S.height
variable {U : MarkedWorld F 0 pins widths} {i z D : ℕ}
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


local notation "prior₁" => ((cur).ports.afterPad k (cur).floor).archive
local notation "support₁" => PhysicalReset.ScheduledCodeRoom G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports.operandLanes (cur).ports.roleLanes
  (cur).ports.venue (cur).ports.io padEnd w prior₁
local notation "padded₁" => (pub).image history
local notation "tag₁" => ((kindCalendar S.rounds S.height).drop i).head?
local notation "full₁" => (resetAt i cur).fullEnd
local notation "issued₁" cap₁:arg sp₁:arg => DatePorts.resetDate G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports (cur).floor w cap₁ sp₁
local notation "ready₁" cap₁:arg sp₁:arg => PhysicalReset.ScheduledReady G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports.operandLanes (cur).ports.roleLanes (cur).ports.venue
  (cur).ports.io padEnd w prior₁ cap₁ sp₁
private theorem realProfiledCalendar (x : (last).Choice) :
    (traces x).path.capFactors = capCalendar G.b S.rounds g S.height ∧
    (traces x).first.placement.cap=256 ∧ (traces x).path.kinds=kindCalendar S.rounds S.height := by
  dsimp only [SeedNamed.traceAt]
  refine ⟨(trace x).calendar, ?_, (trace x).kinds⟩
  let origin := (trace x).origin
  exact source_cap origin

attribute [local irreducible] traceAt
include bus seedDegree degreeRoom before after_ joined in
theorem profiled_reset_entry (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (incoming : Path.Event.incoming (t:=traces walk) evt cur history) :
    ∃(geo : data i) (space : support₁),
      ready₁ geo.capacity space ∧ program i=issued₁ geo.capacity space ∧ (cursor (i+1)).floor=full₁ ∧
      tag₁=some true ∧ full₁<2^w ∧ 8*(menu).receiverWidth G S k i (cur).ports≤payload ∧
      (pub).Runs history ∧ (cur).ports.venue.cap=r.placement.cap ∧
      padded₁ (cur).ports.archive.count.base=(Fintype.card r.V:Computability.VPVNP.BurstRAM.Word w) ∧
      stageVenue r r.valid.host (cur).ports.io (cur).ports.venue.lanes (cur).ports.venue.paidBits padEnd
        (r.venueRoster r.valid.host) padded₁ := by
  let ev : RunTrace.Events traces i := ⟨walk,evt⟩
  have fitAt := profiled_installed X G S ordinary reset branch positive room shorten w fit
    board op frozen drift degree payload lo header initial seed₁ placed₁ i ev
  let dataFor := realProfiledCalendar X G S ordinary reset branch positive room shorten
  have tagsMatch (x : (last).Choice) : (traces x).path.kinds = kindCalendar S.rounds S.height := (dataFor x).2.2
  have gainEq : (menu).gain=g := rfl
  have capMatch : (traces walk).path.capFactors = capCalendar G.b S.rounds (menu).gain S.height :=
    (dataFor walk).1.trans (congrArg (fun z => capCalendar G.b S.rounds z S.height) gainEq.symm)
  have sourceCap : (traces walk).first.placement.cap=256 := (dataFor walk).2.1
  exact registeredResetEntryAt (ts:=traces) (b₀:=menu) (initial:=initial) (walk:=walk)
    (before:=before) (B:=B) (after_:=after_) (joined:=joined) (tagsMatch:=tagsMatch)
    (capMatch:=capMatch) (sourceCap:=sourceCap) (bus:=bus)
    (seedDegree:=seedDegree) (degreeRoom:=degreeRoom) (ram₀:=history) fitAt incoming

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

import OAI.Hierarchy.DescentRegisteredGeometry
import OAI.Hierarchy.DescentNamedAllRegisterMoves

namespace OAI
/-! # Every actual named prefix has its counted state, public memory and next-date geometry -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
set_option quotPrecheck false
open private traceAt_kinds from OAI.Hierarchy.DescentNamedBranchMachine
attribute [local irreducible] Origin.source Origin.archivePackage issued
section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule} {bits : P → ℕ}
    {d k wire hist final w : ℕ} {q ε : ℝ} {Choices : Type*} (traces : Choices → RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position)
local notation "cursor_" => calendar (w:=w) traces b initial
local notation "steps_" => RegisterTimeline.issued (w:=w) traces b
local notation "program_" => instruction (w:=w) traces b initial
private def prefixStateAt (c : Choices) (m : Memory w) (limit : ℕ) (valid : Prop) : Prop :=
  initial.ports.held (traces c).first initial.floor m →
  (∀ i (e : (traces c).path.Event i), Geometry G S b k w i (cursor_ i) → advances traces b initial c m limit valid i e) →
  ∀ {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (before : Path (traces c).first r) (after_ : Path r (traces c).last),
    before.append after_ = (traces c).path → before.selections.length < limit ∨ valid →
    Geometry G S b k w i (cursor_ i) ∧ (cursor_ i).ports.held r
        (DescentDatedAddressBook.floor initial.floor (RegisterTimeline.span steps_ initial) i)
        (DateCode.history program_ m i) ∧ Fintype.card r.V ≤ (cursor_ i).ports.venue.hosts

omit [Fintype P] in
private theorem prefixStateAtHolds
    (fixed : ∀ i (a z : RunTrace.Events traces i) (x y : Move w),
      RegisterTimeline.issued (w:=w) traces b i a (cursor_ i) x → RegisterTimeline.issued (w:=w) traces b i z (cursor_ i) y → x=y)
    (caps : ∀ c, (traces c).path.capFactors=capCalendar G.b S.rounds b.gain S.height)
    (tags : ∀ c, (traces c).path.kinds=kindCalendar S.rounds S.height)
    (seed : Geometry G S b k w 0 initial)
    (placed : ∀ i (e : RunTrace.Events traces i), fitsAt traces b initial (w:=w) i e)
    (c : Choices) (m : Memory w) (limit : ℕ) (valid : Prop) : prefixStateAt traces b initial c m limit valid := by
  intro boot reached U i z D r before after_ joined active
  exact ⟨geometry_prefix traces b initial fixed caps tags seed placed c before after_ joined,
    RegisterTimeline.held_floor traces b initial c m limit valid fixed boot
      (fun j e => reached j e (geometry_on_event traces b initial fixed caps tags seed placed c j e))
      before after_ joined active⟩
end

variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)
variable {n₀ δ : ℕ} (b : RegisterTimeline.Menu n₀ δ) (initial : RegisterTimeline.Position)
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces b initial
local notation "issue" => RegisterTimeline.issued (w:=w) traces b
local notation "prog" => RegisterTimeline.instruction (w:=w) traces b initial


variable (gain : b.gain=g) (grain : b.p=p) (arity : b.f=f)
variable (ready : Geometry G S b k w 0 initial)
variable (placed : ∀i (e : RunTrace.Events (traceAt X G S ordinary reset branch positive room shorten) i),fitsAt (traceAt X G S ordinary reset branch positive room shorten) b initial (w:=w) i e)
local notation "fixed" => all_registered_moves X G S ordinary reset branch positive room shorten w b gain grain arity
include gain in
private theorem register_cap_calendar (c : (last).Choice) :
    (traces c).path.capFactors=capCalendar G.b S.rounds b.gain S.height :=by
  dsimp only [traceAt]
  exact (trace c).calendar.trans (congrArg (fun k => capCalendar G.b S.rounds k S.height) gain.symm)

variable (z : (normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).Pin → Bool) (walk : (Epochs.finish G _ _ (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose).Choice) (m : Memory w)
local notation "limit" => ((ch).rows z).length
local notation "valid" => (ch).read z=some walk
local notation "here" => (fun i l r x y=>fixed i (cursor i) l r x y)
local notation "caps" => register_cap_calendar X G S ordinary reset branch positive room shorten b gain
local notation "tags" => traceAt_kinds X G S ordinary reset branch positive room shorten

attribute [local irreducible] prefixStateAt traceAt
include gain grain arity ready placed in
theorem original_prefix_state : prefixStateAt traces b initial walk m limit valid :=
  prefixStateAtHolds traces b initial here caps tags ready placed walk m limit valid

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

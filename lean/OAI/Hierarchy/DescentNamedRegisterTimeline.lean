import OAI.Hierarchy.DescentRegisteredPrefixRooms
import OAI.Hierarchy.DescentNamedBranchMachine

namespace OAI
/-! # Original branch-independent registers through the first failure of the named ballot -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
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
local notation "trace" => SeedNamed.issued X G S ordinary reset branch positive room shorten
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

attribute [local irreducible] SeedNamed.issued Origin.source

theorem register_moves_same
    (shared : ∀i,∀l r : RunTrace.Events traces i,∀x y : RegisterTimeline.Move w,
      l.2.isReset = false → r.2.isReset = false → issue i l (cursor i) x→issue i r (cursor i) y→x=y) :
    ∀i (l r : RunTrace.Events traces i) x y,issue i l (cursor i) x→issue i r (cursor i) y→x=y :=
  fun i=>RegisterTimeline.same_kind traces b i (cursor i)
    (fun l r=>event_kind X G S ordinary reset branch positive room shorten i l.1 r.1 l.2 r.2) (shared i)

variable (z : (normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).Pin → Bool)
    (walk : (Epochs.finish G _ _ (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose).Choice)
    (m : Memory w)
local notation "limit" => ((ch).rows z).length
local notation "valid" => (ch).read z=some walk

set_option maxHeartbeats 800000 in
theorem issued_prefix_registers
    (shared : ∀i,∀l r : RunTrace.Events traces i,∀x y : RegisterTimeline.Move w,
      l.2.isReset = false → r.2.isReset = false → issue i l (cursor i) x→issue i r (cursor i) y→x=y)
    (ready : Rooms G S b k w 0 initial)
    (placed : ∀i (e : RunTrace.Events traces i),Rooms G S b k w i (cursor i)→
      ∃step : RegisterTimeline.Move w,issue i e (cursor i) step ∧ step.next.floor<2^w ∧
        (e.2.isReset=true→8*b.receiverWidth G S k i (cursor i).ports ≤ b.payload))
    (bootstrap : initial.ports.held (trace walk).origin.source initial.floor m)
    (reached : ∀i (e : (traces walk).path.Event i),Rooms G S b k w i (cursor i)→
      @RegisterTimeline.advances F pins _ G S widths 0 k (S.epochPower^S.priceExponent) s S.length w price fee
        _ traces n₀ δ b initial walk m limit valid i e)
    {U : MarkedWorld F 0 pins widths} {i grain D : ℕ}
    {r : Reached U G price fee S k i grain D (S.epochPower^S.priceExponent) s}
    (before : Path (trace walk).origin.source r) (after : Path r (trace walk).target)
    (joined : before.append after=(trace walk).path)
    (active : before.selections.length < limit ∨ valid) :
    Rooms G S b k w i (cursor i) ∧ (cursor i).ports.held r
      (DescentDatedAddressBook.floor initial.floor (RegisterTimeline.span issue initial) i)
      (DateCode.history prog m i) ∧ Fintype.card r.V≤(cursor i).ports.venue.hosts := by
  let prefixAt : Path (traces walk).first r := by dsimp only [traceAt]; exact before
  let suffixAt : Path r (traces walk).last := by dsimp only [traceAt]; exact after
  have joinedAt : prefixAt.append suffixAt = (traces walk).path := by
    dsimp only [traceAt, prefixAt, suffixAt]
    exact joined
  have seed : initial.ports.held (traces walk).first initial.floor m := by
    dsimp only [traceAt]
    exact bootstrap
  have liveAt : prefixAt.selections.length < limit ∨ valid := by
    dsimp only [prefixAt,traceAt]
    exact active
  let fixed := register_moves_same X G S ordinary reset branch positive room shorten w b initial shared
  exact @RegisterTimeline.prefix_registers F pins _ G S widths 0 k (S.epochPower^S.priceExponent) s
    S.length w price fee _ traces n₀ δ b initial fixed ready placed walk m limit valid seed reached
    U i grain D r prefixAt suffixAt joinedAt liveAt

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

import OAI.Hierarchy.DescentNamedProfiledAdmission
import OAI.Hierarchy.DescentRegisteredRetainedTape
import OAI.Hierarchy.DescentNamedShelfWidths

namespace OAI
/-! # Reading the selected immutable profile at its actual program cut -/
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
local notation "trace" => issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

open DescentDatedAddressBook
variable {n₀ δ : ℕ} (board : NonlinearExpanders.Graph n₀ δ) (op : RotorSpec)
    (frozen drift degree payload lo header : ℕ) (initial : RegisterTimeline.Position)
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial

open DescentPackedEpochShelves DescentPackedProfileTape DescentPackedProfileInstall
local notation "pitch" => DescentPackedEpochShelves.grain (payload/2) G.C
local notation "issue" => RegisterTimeline.issued (w:=w) traces menu
local notation "cpu" => RegisterTimeline.instruction (w:=w) traces menu initial


set_option maxHeartbeats 900000 in
theorem registered_profile_room (beforeHeader:lo+extent pitch (ch).layout≤header)
    (lower:header< initial.floor) (c:(last).Choice)
    {W:MarkedWorld F 0 pins widths} {i z D z' D':ℕ} {rate:ℝ} {nonneg:0≤fee}
    {prior:Reached W G price fee S k i z D (S.epochPower^S.priceExponent) s} {T:StageInput W G rate fee}
    {choice:(T.result nonneg).Choice} {norm:Normalize ((T.result nonneg).state choice)}
    {next:Reached norm.result G price fee S k (i+1) z' D' (S.epochPower^S.priceExponent) s}
    (ticket:OrdinaryLink prior nonneg T choice norm next)
    (before:Path (trace c).origin.source prior) (after:Path next (trace c).target)
    (joined:(before.ordinary ticket).append after=(trace c).path) (space:(cursor i).floor<2^w) :
    header≤(cursor i).floor ∧ (sourceBank ((menu).profile i) ((menu).seats i) pitch).Fits w (cursor i).floor:=by
  obtain ⟨sl,listed,atRow,_,_⟩:=registered_profile_exists X G S ordinary reset branch positive room shorten
    w fit payload lo c ticket before after joined
  have printed:=RegisterTimeline.fromProfiles_at G S board op k frozen p f g drift degree payload lo header
    (ch).layout i sl atRow
  have earlier:=lower.le.trans (RegisterTimeline.initial_below_cursor issue initial i)
  refine ⟨earlier,?_⟩
  rw [printed.1,printed.2.1]
  exact shelf_fits sl listed (beforeHeader.trans earlier) space

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

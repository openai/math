import OAI.Hierarchy.DescentNamedProfileSeatFit
import OAI.Hierarchy.DescentObservedStageInputs

namespace OAI
/-! # Physical site names, bounded counters and overflow-free seat counts on the original cut -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
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

open StarKeys DescentStageEdgeReceipt
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

theorem issued_observation_inputs (c : (last).Choice) {W : MarkedWorld F 0 pins widths}
    {i z D z' D' : ℕ} {rate : ℝ} {nonneg : 0 ≤ fee}
    {prior : Reached W G price fee S k i z D (S.epochPower^S.priceExponent) s} {T : StageInput W G rate fee}
    {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' (S.epochPower^S.priceExponent) s}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path (trace c).origin.source prior) (after : Path next (trace c).target)
    (cut : (before.ordinary ticket).append after=(trace c).path)
    (height : 0<S.height) (age : i≤S.length)
    (entry : Source (ch).Pin) (header : (ch).layout[before.selections.length]?=some entry) :
    prior.placement.SiteNamed (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)) ∧
    prior.placement.wire*(prior.placement.z*G.b)*prior.placement.cap<2^(S.censusBits p) ∧
    ∃actual : (prior.placement.stage.result nonneg).Choice, HEq choice actual ∧
      Fintype.card (NativePair W.graph W.core (scanHomeAt nonneg prior.placement.stage)
        (scanColorAt nonneg prior.placement.stage) prior.placement.cap) ≤ entry.seats := by
  exact ⟨((trace c).origin.names_on_path before).1,
    ticket.observed_mass before after cut (trace c).issuedGrains height age rfl branch,
    issued_profile_seats X G S ordinary reset branch positive room shorten w fit c ticket before after cut entry header⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

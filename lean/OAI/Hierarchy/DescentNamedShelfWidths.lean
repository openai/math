import OAI.Hierarchy.DescentNamedNormalizedChart
import OAI.Hierarchy.DescentEpochShelfWidths

namespace OAI
/-! Each allocated named selector shelf uses the genuine profile width and batch capacity. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentColonies DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentGL DescentCompiler DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open scoped Classical BigOperators
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
local notation "cert" => SeedNamed.normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "digits" => S.initialDigits ordinary.radix
local notation "q" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)

local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => issued X G S ordinary reset branch positive room shorten

variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)

local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

include fit in
theorem normalized_shelf_widths : ∀v∈(ch).layout,v.C=G.C ∧ v.seats≤S.batch :=by
  apply epoch_widths G _ _ run order (seedChart X S.copies s w fit)
  · intro v empty
    exact (List.not_mem_nil empty).elim
  · intro c sel seen
    let b:=trace c
    exact path_paid G b.path ordinary.radix le_rfl sel (by simpa only [b.selections] using seen)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

import OAI.Hierarchy.DescentNamedNormalizedChart
import OAI.Hierarchy.DescentPackedEpochCountReads

namespace OAI
/-! # Measured counts at the named path’s actual ordinal registers -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentSixParty DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalEpochChart DescentTerminalEpochDecoder DescentSeedRoot Catalyst Computability.BorderVNP.Crossing
open DescentPackedEpochShelves Computability.VPVNP.BurstRAM
open scoped Classical
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
local notation "rs" => (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose
local notation "ow" => inputOrder X G S ordinary reset branch positive room shorten
local notation "q" => S.firstWidth G.b p
variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
variable (z : (normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).Pin→Bool)
local notation "choice_" => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow z
local notation "path_" => (SeedNamed.issued X G S ordinary reset branch positive room shorten choice_).path.selections

theorem issued_count_words (lo R : ℕ) (count exterior : ℕ→ℕ) (m : Memory w)
    (physical : ∀i,i < ((ch).rows z).length→∀v,(path_)[i]?=some v→(m (count i)).val=selectionCount G v) :
    List.IsPrefix (((ch).rows z).map Observation.count)
      ((controls lo G.C R (ch).layout count exterior).map fun s=>(m s.banks.count.base).val) :=
  native_prefix ch z lo G.C R count exterior m path_ (selectionCount G)
    (packedChart_prefix X G S ordinary reset branch positive room shorten w fit z) physical

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

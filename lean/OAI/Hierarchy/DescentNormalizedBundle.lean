import OAI.Hierarchy.DescentChronologicalBundle
import OAI.Hierarchy.DescentBundleSeedEpoch
import OAI.Hierarchy.DescentNormalizedEpochs

namespace OAI
/-! # Bundled local records of the same run that meets the final frontier bound -/
namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory DescentSixParty DescentCompiler DescentInitialHost DescentMixedRouter
open DescentResetInvoice Catalyst Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b≤2^S.capGain) (positive : 0<p) (room : 10*(X.size+1)≤S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds≤1/2)
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "strideBound" => max 1 (max reset.bitsR (C*reset.bitsR))

/-- The selection is precisely the run delivering the independent-copy tensor identity,
terminal tether/core budget and retained group state in `normalized_epochs_issued`. -/
def normalizedRows (c : (Epochs.finish G _ _ (cert).choose).Choice) :
    Retained p strideBound ((Epochs.finish G _ _ (cert).choose).state c) :=
  seedEpochs X S.copies (S.firstWidth G.b p) positive (le_max_left _ _)
    (dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b) reset.menu (le_refl _)
    S (cert).choose (cert).choose_spec.1 c

/-- The same scalar-node ordering that the issued code reads also carries the actual
complete p-bit operand descriptors, including the rank and span of every fetched word. -/
def normalizedIssuedRows (c : (Epochs.finish G _ _ (cert).choose).Choice) := ((cert).choose_spec.2.2.choose_spec.choose_spec c).choose

/-- The runtime tape has one shared pair numbering before each motif profile is selected. -/
def normalizedIssuedOrders := (cert).choose_spec.2.2.choose

theorem normalizedIssuedRanked (c : (Epochs.finish G _ _ (cert).choose).Choice) :
    (normalizedIssuedRows X G S ordinary reset branch positive room shorten c).path.ranked=
      Chronology.epochsRanked G (cert).choose (normalizedIssuedOrders X G S ordinary reset branch positive room shorten) c :=
  ((cert).choose_spec.2.2.choose_spec.choose_spec c).choose_spec.1

/-- The physical input pair directory belongs to the same run and branch as the issued output pairs. -/
def normalizedIssuedInputOrders := (cert).choose_spec.2.2.choose_spec.choose

theorem normalizedIssuedInputRanked (c : (Epochs.finish G _ _ (cert).choose).Choice) :
    (normalizedIssuedRows X G S ordinary reset branch positive room shorten c).path.inputRanked=
      Chronology.epochsRanked G (cert).choose (normalizedIssuedInputOrders X G S ordinary reset branch positive room shorten) c :=
  ((cert).choose_spec.2.2.choose_spec.choose_spec c).choose_spec.2.1

theorem normalizedIssuedCapFactors (c : (Epochs.finish G _ _ (cert).choose).Choice) :
    (normalizedIssuedRows X G S ordinary reset branch positive room shorten c).path.capFactors=
      capCalendar G.b S.rounds g S.height :=
  ((cert).choose_spec.2.2.choose_spec.choose_spec c).choose_spec.2.2.1.1

theorem normalizedIssuedRotor (c : (Epochs.finish G _ _ (cert).choose).Choice) :
    (normalizedIssuedRows X G S ordinary reset branch positive room shorten c).path.OnlyRotor (RotorSpec.ofRates reset) :=
  ((cert).choose_spec.2.2.choose_spec.choose_spec c).choose_spec.2.2.1.2


def normalizedIssuedShape (c : (Epochs.finish G _ _ (cert).choose).Choice) :
    let branchRow:=normalizedIssuedRows X G S ordinary reset branch positive room shorten c
    WorldShape p strideBound ((NativeBranch.archive X G S branchRow positive).bit) := by
  let row:=normalizedIssuedRows X G S ordinary reset branch positive room shorten c
  have whole : p∣S.firstWidth G.b p := dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b
  exact archiveShape positive (le_max_left _ _) (fun _=>by simpa using whole) _
    (seedRetained X S.copies (S.firstWidth G.b p) positive (le_max_left _ _) whole _).shape
    row.path (row.path.recorded_whole p row.recorded) row.aligned

end
end Hierarchy.DescentBundleHistory

end OAI

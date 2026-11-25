import OAI.Hierarchy.DescentNamedEpochChart
import OAI.Hierarchy.DescentNamedEpochs
import OAI.Hierarchy.DescentTerminalPairedOrders

namespace OAI
/-! # The canonical incoming selector tape uses the genuine named epochs' input order -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentColonies DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentGL DescentCompiler DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch CorrectionFrame Computability.BorderVNP.Crossing
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
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)

def inputOrder := (cert).choose_spec.2.2.choose_spec.choose
def outputOrder := (cert).choose_spec.2.2.choose
def issued (c : (last).Choice) := ((cert).choose_spec.2.2.choose_spec.choose_spec c).choose
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => issued X G S ordinary reset branch positive room shorten

theorem issued_inputRanked (c : (last).Choice) : (trace c).path.inputRanked=epochsRanked G run order c :=
  ((cert).choose_spec.2.2.choose_spec.choose_spec c).choose_spec.2.1

theorem issued_outRanked (c : (last).Choice) : (trace c).path.ranked=
    epochsRanked G run (outputOrder X G S ordinary reset branch positive room shorten) c :=
  ((cert).choose_spec.2.2.choose_spec.choose_spec c).choose_spec.1

theorem seats : epochSeats G _ _ run ≤ S.length*S.batch := by
  apply paid_by_paths (q:=price) G _ _ run ordinary.radix
  intro c
  let b:=trace c
  exact ⟨_,_,_,_,_,_,_,_,_,_,b.origin.source,b.target,b.path,le_rfl,b.selections⟩

variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)

def normalizedPackedChart := packedChart G _ _ X S.copies s w fit digits run order
def normalizedRoute := route G _ _ X S.copies s w fit digits run order
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
local notation "reach" => normalizedRoute X G S ordinary reset branch positive room shorten w fit

local instance : Fintype (ch).Pin := (ch).finite

theorem packedChart_once (c : (last).Choice) : ∃!z,(ch).read z=some c := (ch).once c

theorem packedChart_card : Fintype.card (ch).Pin ≤
    80*S.copies*(X.size+1)*((s).log2+1)+(S.length*S.batch)*DescentTerminalEpochBits.width G.C := by
  rw [show Fintype.card (ch).Pin=Fintype.card (Select X S.copies s)+epochSeats G _ _ run*DescentTerminalEpochBits.width G.C from
    pin_count G _ _ X S.copies s w fit digits run order]
  exact Nat.add_le_add (select_bound X S.copies s) (Nat.mul_le_mul_right _ (seats X G S ordinary reset branch positive room shorten))

theorem packedChart_fields (z : (ch).Pin→Bool) (c : (last).Choice) (hit : (ch).read z=some c) :
    (ch).layout.map (rawAt z)=(trace c).path.inputRanked.map (issuedProfile G) := by
  rw [issued_inputRanked]
  exact fields_of_read G _ _ X S.copies s w fit digits run order z c hit

theorem packedChart_prefix (z : (ch).Pin→Bool) :
    List.IsPrefix ((ch).counts z) ((trace ((reach).follow z)).path.selections.map (selectionCount G)) := by
  rw [(trace ((reach).follow z)).selections]
  exact raw_prefix G _ _ X S.copies s w fit digits run order z

theorem packedChart_seed (z : (ch).Pin→Bool) (c : (last).Choice) (hit : (ch).read z=some c) (key : CountKey X S.copies) :
    (rawCount X (z∘(ch).seed) key).val=selected X (Epochs.seedChoice G _ _ (H:=initial X S.copies s (S.groupCount 0) k digits) (J:=S.height)
      (t:=S.rounds) (h:=h) (C:=C) (Ht:=GroupStage.depthBound (atRound S.rounds) n f g) run c) key :=
  seed_read G _ _ X S.copies s w fit digits run order z c hit key

theorem packedChart_weight (z : (ch).Pin→Bool) (c : (last).Choice) (hit : (ch).read z=some c) :
    TypedWiring.value (DescentTerminalSeedChip.circuit X (ch).seed) z=(last).weight c :=
  seed_numerator G _ _ X S.copies s w fit digits run order z c hit

theorem packedChart_coeff (x : Port ((S.copies*s)*nP) (copiesWidth (S.copies*s) X.width)→Bool) :
    let input:=packagePins X S.copies s x
    let pay:=fun c : (last).Choice=>(last).weight c*((last).state c).value input
    (∑z : (ch).Pin→Bool,((ch).read z).elim 0 pay)=(independentCopies (S.copies*s) X).coeff x := by
  intro input pay
  exact (weight_sum ch pay).trans ((cert).choose_spec.2.1 x)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

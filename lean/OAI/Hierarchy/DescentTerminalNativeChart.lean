import OAI.Hierarchy.DescentTerminalEpochRoutes
import OAI.Hierarchy.DescentTerminalEpochLayoutBill
import OAI.Hierarchy.DescentNormalizedBundle

namespace OAI
/-! # The terminal decoder for the run with the independent-copy coefficient identity -/
namespace Hierarchy.DescentBundleHistory
open DescentSixParty DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalEpochDecoder DescentTerminalEpochChart DescentTerminalEpochBits
open DescentSeedRoot Catalyst Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
local notation "seedWidth" => S.firstWidth G.b p
local notation "historyRate" => (1/((seedWidth:ℝ)*((S.epochPower:ℝ)^S.priceExponent)):ℝ)
local notation "r" => (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose
local notation "order" => normalizedIssuedOrders X G S ordinary reset branch positive room shorten
variable (w : ℕ) (word : S.firstWidth G.b p < 2^w)

/-- No pair order, maximal padding assumption, or history is chosen by the caller. -/
def normalizedChart := actualWith G _ _ X S.copies seedWidth w word r order

theorem normalizedSeats : epochSeats G _ _ r ≤ S.length*S.batch := by
  apply paid_by_paths (q:=historyRate) G _ _ r ordinary.radix
  intro c
  let b:=normalizedIssuedRows X G S ordinary reset branch positive room shorten c
  exact ⟨_,_,_,_,_,_,_,_,_,_,b.source,b.target,b.path,le_rfl,b.selections⟩

local notation "b" => normalizedChart X G S ordinary reset branch positive room shorten w word

theorem normalizedChart_extent :
    DescentTerminalEpochHeader.extent (b).layout ≤ 2*(S.length*S.batch)+S.length :=
  physical_extent G _ _ X S.copies seedWidth w word S r order
    (normalizedSeats X G S ordinary reset branch positive room shorten)

theorem normalizedChart_card : Fintype.card (b).Pin ≤ 80*S.copies*(X.size+1)*((seedWidth).log2+1) +
    (S.length*S.batch)*DescentTerminalEpochBits.width G.C := by
  have card:=epochsWith_size G _ _ r order (seedChart X S.copies seedWidth w word)
  change Fintype.card (b).Pin=Fintype.card (Select X S.copies seedWidth)+epochSeats G _ _ r*DescentTerminalEpochBits.width G.C at card
  rw [card]
  exact Nat.add_le_add (select_bound X S.copies seedWidth)
    (Nat.mul_le_mul_right _ (normalizedSeats X G S ordinary reset branch positive room shorten))

theorem normalizedChart_seed (z : (b).Pin→Bool) (t : (Epochs.finish G _ _ r).Choice) (hit : (b).read z=some t)
    (key : CountKey X S.copies) :
    (rawCount X (z∘(b).seed) key).val=selected X (Epochs.seedChoice G _ _ r t) key :=
  actualWith_seed G _ _ X S.copies seedWidth w word r order z t hit key

theorem normalizedChart_once (t : (Epochs.finish G _ _ r).Choice) : ∃!z,(b).read z=some t := (b).once t

/-- Supply the memory comparison only through the first still-reached deck,
even if its raw profile or padding is malformed. The reference path includes
that deck's true inherited accepted-pair counter. -/
theorem normalizedChart_prefix (z : (b).Pin→Bool) :
    let chosen:=(actualRoute G _ _ X S.copies seedWidth w word r order).follow z
    let issued:=normalizedIssuedRows X G S ordinary reset branch positive room shorten chosen
    List.IsPrefix ((b).counts z) (issued.path.selections.map (selectionCount G)) := by
  let chosen:=(actualRoute G _ _ X S.copies seedWidth w word r order).follow z
  let issued:=normalizedIssuedRows X G S ordinary reset branch positive room shorten chosen
  change List.IsPrefix ((b).counts z) (issued.path.selections.map (selectionCount G))
  rw [issued.selections]
  exact raw_prefix G _ _ X S.copies seedWidth w word r order z

end
end Hierarchy.DescentBundleHistory

end OAI

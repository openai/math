import OAI.Hierarchy.DescentTerminalPairedOrders
import OAI.Hierarchy.DescentPackedProfileTape

namespace OAI
/-! # Complete incoming selector stream for a chronological native stage -/
namespace Hierarchy.DescentTerminalEpochDecoder
open DescentSixParty DescentSixParty.Chronology DescentTerminalEpochChart DescentPackedProfileTape
open DescentKernelHistory.BitDescription DescentTerminalEpochFlags
open scoped Classical
noncomputable section
variable {A : Type} (s : Source A) (z : A→Bool)

theorem cell_read (j : ℕ) : (cell s.pin z j).val=rawAt z s j := by
  by_cases inside : j < s.seats
  · rw [rawAt,dite_eq_left inside]
    exact active s.pin z ⟨j,inside⟩
  · simp [rawAt,inside,inactive s.pin z (not_lt.mp inside)]

theorem original_fields {F P : Type} [Field F] {d : ℕ} {bs : P→ℕ} {G : PoweredGadget F} {ε : ℝ}
    (ts : List (Source A)) (rs : List (RankedSelection F P d bs G ε))
    (same : ts.map (rawAt z)=rs.map (issuedProfile G)) {r : ℕ} {v : RankedSelection F P d bs G ε}
    (origin : ts[r]?=some s) (stage : rs[r]?=some v) :
    ∀j,(cell s.pin z j).val=profileAt v.2 ((scannedRows v.1.nonneg v.1.stage).profile v.1.choice) j := by
  have h:=congrArg (fun t=>t[r]?) same
  simp only [List.getElem?_map,origin,stage,Option.map_some,Option.some.injEq] at h
  intro j
  exact (cell_read s z j).trans (congrFun h j)

end
end Hierarchy.DescentTerminalEpochDecoder

namespace Hierarchy.DescentBundleHistory
open DescentSixParty DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalEpochDecoder DescentTerminalEpochChart DescentTerminalEpochBits
open DescentKernelHistory.BitDescription DescentSeedRoot Catalyst Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
local notation "width_" => S.firstWidth G.b p
local notation "r" => (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose
variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)
local notation "b" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

/-- All globally indexed digits, including unused ordinals and the guard word,
come directly from the original selector of this same abstract branch. -/
theorem packedChart_at (z : (b).Pin→Bool) (c : (Epochs.finish G _ _ r).Choice) (ok : (b).read z=some c)
    (i : ℕ) (a : Source (b).Pin) (v : Chronology.RankedSelection F _ _ _ G _) (header : (b).layout[i]?=some a)
    (entered : (normalizedIssuedRows X G S ordinary reset branch positive room shorten c).path.inputRanked[i]?=some v) :
    ∀j,(DescentPackedProfileTape.cell a.pin z j).val=
      profileAt v.2 ((scannedRows v.1.nonneg v.1.stage).profile v.1.choice) j :=
  original_fields a z _ _ (packedChart_fields X G S ordinary reset branch positive room shorten w fit z c ok) header entered

end
end Hierarchy.DescentBundleHistory

end OAI

import OAI.Hierarchy.DescentNamedCohortFiber
import OAI.Hierarchy.DescentTerminalGrainStreams
import OAI.Hierarchy.DescentTerminalCohortRanks

namespace OAI
/-! # Frozen-cohort counts on every host equal the number of actual public grains -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S radix R r c) (hp : 0<p)

open DescentGL DescentColonies DescentExterior PinCohorts
local notation "s" => S.firstWidth G.b p
local notation "SeedPin" => Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))


namespace Branch
variable {tail : ℕ} (base : S.baseGroups=2^tail)
local notation "trace" => pinSpine X G S b hp base
local notation "E" => Fintype.card (Port P X.width)
local notation "H" => S.hostSize S.length
local notation "a" => S.groupWidth k tail S.length+k
local notation "N" => ((Epochs.finish G hu he r).state c).graph
local notation "A" => b.target.placement
local notation "f" => b.path.frozen
local notation "Cohort" => Fin (E*2^f)

open Computability.BorderVNP.FragmentBucket DescentTerminalExteriorHeaders DescentTerminalCohortRanks
open scoped BigOperators

/-- Every single original named pin is uniquely its final active word and frozen cohort. -/
def homePins (i : Fin H) : {z:SeedPin // b.target.home ((N).attach z)=i} ≃
    Bits a × {j:Cohort // cohortHome X G S b hp base j=i} where
  toFun z := (active b.target base radix z.val,⟨cohort X G S b hp base z.val,by
    have same:=home_cohort X G S b hp base (active b.target base radix z.val) (cohort X G S b hp base z.val)
    rw [at_cohort] at same
    exact same.symm.trans z.property⟩)
  invFun t := ⟨atCohort X G S b hp base t.1 t.2.val,
    (home_cohort X G S b hp base _ _).trans t.2.property⟩
  left_inv z := Subtype.ext (at_cohort X G S b hp base _)
  right_inv t := Prod.ext (terminal_active X G S b hp base _ _ _)
    (Subtype.ext (cohort_at X G S b hp base _ _))

/-- The tally in the published cohort RAM is per active group; this one fixed multiplier
counts all physical active group and block positions and all p-grains in each original wire. -/
def publicRate := 2^a*(S.firstWidth G.b p / p)

theorem site_public_grains (i : Fin H) :
    siteMass (N) b.target.home i / p =
      count (cohortHome X G S b hp base) i * publicRate G S (k:=k) (tail:=tail) (p:=p) := by
  classical
  have localCard : Fintype.card {z:SeedPin // b.target.home ((N).attach z)=i}=
      2^a*count (cohortHome X G S b hp base) i := by
    rw [Fintype.card_congr (homePins X G S b hp base i),Fintype.card_prod,card_bits,
      Fintype.card_congr (numbered (cohortHome X G S b hp base) i),Fintype.card_fin]
  have mass : siteMass (N) b.target.home i=(2^a*count (cohortHome X G S b hp base) i)*s := by
    rw [←localCard,Fintype.card_subtype]
    change (∑z:SeedPin, if b.target.home ((N).attach z)=i then s*1 else 0)=_
    simp only [Nat.mul_one, ←Finset.sum_filter, Finset.sum_const, Nat.nsmul_eq_mul]
  have div : p∣s:=by
    unfold DescentCompiler.AtomSchedule.firstWidth DescentCompiler.AtomSchedule.grainAt
    exact (dvd_mul_right p _).trans (dvd_mul_right _ _)
  rw [mass,Nat.mul_div_assoc _ div]
  simp only [publicRate];ring

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

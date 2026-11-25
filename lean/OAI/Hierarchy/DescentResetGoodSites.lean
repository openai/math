import OAI.Hierarchy.DescentColonies

namespace OAI
/-! # Paying finitely many good physical sites by their distinct base names -/

namespace Hierarchy.DescentRotor.Physical

open DescentColonies
open scoped BigOperators Classical
noncomputable section
variable {V Q : Type*} [Fintype V] [Fintype Q]

private theorem good_site_bill (good : Finset Q) (budget : Q→ℝ) (pay : ℝ)
    (away : ∀ v, v∉good → budget v=0) (each : ∀ v,v∈good → budget v≤pay) :
    (∑v,budget v) ≤ (good.card:ℝ)*pay := by
  classical
  calc
    (∑v,budget v) = ∑v∈good,budget v :=
      (Finset.sum_subset (Finset.subset_univ _) fun v _ h => away v h).symm
    _ ≤ ∑_v∈good,pay := Finset.sum_le_sum each
    _ = _ := by simp

/-- Good sites have distinct original base names and all other sites have zero charge. -/
theorem good_site_pay_le (b : V→ℕ) (good : Finset Q) (budget : Q→ℝ) {pay : ℝ}
    (identified : ∃ name : good→Σ v,Block (b v),Function.Injective name)
    (away : ∀ v,v∉good → budget v=0) (each : ∀ v,v∈good → budget v≤pay)
    (nonneg : 0≤pay) : (∑v,budget v) ≤ pay*∑v,(2:ℝ)^b v := by
  obtain ⟨name,inj⟩ := identified
  have count : good.card ≤ ∑v,(2:ℕ)^b v := by
    simpa only [Fintype.card_coe,Fintype.card_sigma,Block,Fintype.card_fin]
      using Fintype.card_le_of_injective name inj
  have bound : (good.card:ℝ) ≤ ∑v,(2:ℝ)^b v := by exact_mod_cast count
  exact (good_site_bill good budget pay away each).trans
    ((mul_le_mul_of_nonneg_right bound nonneg).trans_eq (mul_comm ..))

/-- With a separate site at each of the two ends of a named base, its charge is
counted at most twice. -/
theorem paired_good_site_pay_le (b : V→ℕ) (good : Finset Q) (budget : Q→ℝ) {pay : ℝ}
    (identified : ∃ name : good→Bool × (Σ v,Block (b v)),Function.Injective name)
    (away : ∀ v,v∉good → budget v=0) (each : ∀ v,v∈good → budget v≤pay)
    (nonneg : 0≤pay) : (∑v,budget v) ≤ 2*(pay*∑v,(2:ℝ)^b v) := by
  obtain ⟨name,inj⟩ := identified
  have count : good.card ≤ 2*∑v,(2:ℕ)^b v := by
    simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_bool,Fintype.card_sigma,Block,Fintype.card_fin]
      using Fintype.card_le_of_injective name inj
  have bound : (good.card:ℝ) ≤ 2*∑v,(2:ℝ)^b v := by exact_mod_cast count
  exact (good_site_bill good budget pay away each).trans
    ((mul_le_mul_of_nonneg_right bound nonneg).trans_eq (by ring))

end
end Hierarchy.DescentRotor.Physical

end OAI

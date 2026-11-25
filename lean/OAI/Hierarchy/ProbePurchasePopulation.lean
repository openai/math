import OAI.Hierarchy.ProbeDisjointStrips

namespace OAI
/-! # The total number of purchased tests fits the original payload normalization -/

namespace Hierarchy.ProbeStage
open AdaptiveProbe
open scoped BigOperators Classical
noncomputable section

/-- At the affordable public scale H exceeds the number of routing stages. -/
theorem stages_le_purchase {T : ℝ} (stages k : ℕ) (hk : 0<k) (hT : 0<T)
    (small : (stages:ℝ)*T≤1/4) : stages≤⌈32*(k:ℝ)/T⌉₊ := by
  have one : (1:ℝ)≤k := by exact_mod_cast hk
  have big : (stages:ℝ) ≤ 32*(k:ℝ)/T := (le_div_iff₀ hT).2 (by linarith)
  exact_mod_cast big.trans (Nat.le_ceil _)

variable {h d k : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : StageAt h d → (Fin k × Bool) → Finset (Fin (2^h)))

/-- Charged tests across *all* signs and groups together have at most n genuine
rows. The live rows can be padded to n words when feeding the global failure gate. -/
theorem purchased_card_le (unique : ∀ s c c' r, r∈marked s c → r∈marked s c' → c=c')
    (stages : (permutationFabric h d).shapes.length≤depth+1) :
    Fintype.card (LiveChains S π depth marked) ≤ 2^h := by
  have count := Fintype.card_le_of_embedding (plainRows S π depth marked unique)
  simp only [Fintype.card_prod,Fintype.card_fin] at count
  change Fintype.card (LiveChains S π depth marked)*(depth+1) ≤ (permutationFabric h d).shapes.length * 2^h at count
  have bound := count.trans (Nat.mul_le_mul_right (2^h) stages)
  rw [Nat.mul_comm (depth+1)] at bound
  exact Nat.le_of_mul_le_mul_right bound (by omega)

/-- Original payload normalization of the accumulated per-row approximation losses
in the replay mode. The physical fixed-slot board can be arbitrarily more padded. -/
theorem purchased_error_sum (unique : ∀ s c c' r, r∈marked s c → r∈marked s c' → c=c')
    (stages : (permutationFabric h d).shapes.length≤depth+1) (trueValue rounded : LiveChains S π depth marked → ℝ)
    {ε : ℝ} (he : 0≤ε) (close : ∀j,|trueValue j-rounded j|≤ε) :
    |(∑j,trueValue j)-(∑j,rounded j)| ≤ (2:ℝ)^h*ε := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |trueValue j-rounded j| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _ : LiveChains S π depth marked, ε := Finset.sum_le_sum fun j _ => close j
    _ = (Fintype.card (LiveChains S π depth marked):ℝ)*ε := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast purchased_card_le S π depth marked unique stages) he

end
end Hierarchy.ProbeStage

end OAI

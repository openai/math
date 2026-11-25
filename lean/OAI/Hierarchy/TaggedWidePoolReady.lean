import OAI.Hierarchy.TaggedDyadicBanks
import OAI.Hierarchy.TaggedGapScale

namespace OAI
/-! # Cutoffs and index words for the purchased compactors -/

noncomputable section
namespace Hierarchy.Tagged
open TaggedShorterBudget Filter
open scoped Topology

/-- Uniform in both the actual price and the dimension of the candidate
array, the paid near and far compactor problems exceed the expander cutoff.
Both address words fit in twice the parent height. -/
theorem eventually_pool_ready (cutoff : ℕ) (K : ℝ) {c₀ T : ℝ} (positive : 0<c₀)
    (hT : 0<T) (small : T≤1/2) (t : ℕ→ℕ)
    (ratio : Tendsto (fun h=>(t h:ℝ)/h) atTop (𝓝 T)) :
    ∀ᶠ h : ℕ in atTop, ∀ (c : ℝ) (S D : ℕ), c₀≤c → 0<D → D≤2^h →
      (S:ℝ)*D ≤ K*(2:ℝ)^h →
      let M := ⌈6*c*(2:ℝ)^h/(2:ℝ)^(t h)⌉₊
      t h≤h ∧ cutoff≤2*2^(t h) ∧ cutoff≤2*M ∧ Nat.log 2 S≤2*h ∧ Nat.log 2 D≤2*h := by
  have high : Tendsto (fun h : ℕ=>(h:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have grow := high.num hT ratio
  have tiny := eventually_bank_small hT small (c:=6*c₀/((cutoff:ℝ)+1)) (by positivity) id t high ratio
  have bound := eventually_bank_small hT small (c:=1) zero_lt_one id t high ratio
  filter_upwards [grow.eventually_ge_atTop (cutoff:ℝ),tiny,bound,GapScale.eventual_polynomial 0 K 0 (by norm_num)]
    with h large paid ht price
  intro c S D hc pos cap slots M
  have th : t h≤h := by
    have a : (2:ℕ)^(t h) ≤ 2^h := by exact_mod_cast (show (2:ℝ)^(t h)≤(2:ℝ)^h by simpa using ht)
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp a
  have cut : cutoff≤t h := by exact_mod_cast large
  have tall : cutoff≤2*2^(t h) := by
    have bound := Nat.lt_two_pow_self (n:=t h)
    omega
  have posT : 0<(2:ℝ)^(t h) := by positivity
  have enough : ((cutoff:ℝ)+1)*(2:ℝ)^(t h) ≤ 6*c*(2:ℝ)^h := by
    have paid' : (2:ℝ)^(t h) ≤ (6*c₀*(2:ℝ)^h)/((cutoff:ℝ)+1) := by
      simpa [div_mul_eq_mul_div] using paid
    have raw := (le_div_iff₀ (by positivity : 0<(cutoff:ℝ)+1)).mp paid'
    calc
      _ ≤ 6*c₀*(2:ℝ)^h := by simpa only [mul_comm ((cutoff:ℝ)+1)] using raw
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) (by positivity)
  have massive : (cutoff:ℝ)+1≤M :=
    ((le_div_iff₀ posT).mpr enough).trans (Nat.le_ceil _)
  have mBound : cutoff≤2*M := by
    have m : cutoff+1≤M := by exact_mod_cast massive
    omega
  have discounted : K≤(2:ℝ)^h := by simpa [gap] using price
  have sN : S≤(2:ℕ)^(2*h) := by
    have first : (S:ℝ) ≤ (S:ℝ)*D := le_mul_of_one_le_right (Nat.cast_nonneg _) (by exact_mod_cast (Nat.succ_le_of_lt pos))
    have second : (S:ℝ) ≤ (2:ℝ)^(2*h) := by
      rw [two_mul,pow_add]
      exact (first.trans slots).trans (mul_le_mul_of_nonneg_right discounted (by positivity))
    exact_mod_cast second
  have dN : D≤2^(2*h) := cap.trans (Nat.pow_le_pow_right (by decide) (show h≤2*h by omega))
  refine ⟨th,tall,mBound,?_,?_⟩
  · simpa only [Nat.log_pow (by decide : 1<2)] using Nat.log_mono_right (b:=2) sN
  · simpa only [Nat.log_pow (by decide : 1<2)] using Nat.log_mono_right (b:=2) dN

end Hierarchy.Tagged

end
end OAI

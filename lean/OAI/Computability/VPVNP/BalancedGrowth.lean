import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Comparing the exponential growth of finitely many balanced cuts

In Section 4.2 each cut contributes a fixed multiplicative factor times an
exponential in the tensor-power index. Strictly smaller exponents make their
sum negligible compared with the lower bound for the full tensor power.
-/

namespace OAI
namespace Computability
namespace VPVNP

open Filter Topology

variable {ι : Type*}

/-- After division by the target power, the finite sum tends to zero. -/
theorem tendsto_weighted_pow_ratio (cuts : Finset ι) (weight base : ι → ℝ) (target : ℝ)
    (ht : 0 < target) (hb : ∀ i ∈ cuts, 0 ≤ base i ∧ base i < target) :
    Tendsto (fun h : ℕ => (∑ i ∈ cuts, weight i * base i ^ h) / target ^ h) atTop (𝓝 0) := by
  have hi (i : ι) (hic : i ∈ cuts) :
      Tendsto (fun h : ℕ => weight i * (base i / target) ^ h) atTop (𝓝 0) := by
    have lower := div_nonneg (hb i hic).1 ht.le
    have upper : base i / target < 1 := (div_lt_one ht).mpr (hb i hic).2
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one lower upper).const_mul (weight i)
  simpa [div_eq_mul_inv, mul_pow, inv_pow, Finset.sum_mul, mul_assoc] using tendsto_finsetSum cuts hi

/-- At every sufficiently large power the total cut contribution is less than any
fixed positive fraction of the target power. -/
theorem eventually_weighted_pow_lt (cuts : Finset ι) (weight base : ι → ℝ) (target ε : ℝ)
    (ht : 0 < target) (hε : 0 < ε) (hb : ∀ i ∈ cuts, 0 ≤ base i ∧ base i < target) :
    ∀ᶠ h : ℕ in atTop, ∑ i ∈ cuts, weight i * base i ^ h < ε * target ^ h := by
  filter_upwards [(tendsto_weighted_pow_ratio cuts weight base target ht hb).eventually_lt_const hε]
    with h hlt using (div_lt_iff₀ (pow_pos ht h)).mp hlt

/-- Strict comparison with the target, in terms of the spectral values themselves. -/
theorem eventually_weighted_pow_lt_target (cuts : Finset ι) (weight base : ι → ℝ) (target : ℝ)
    (ht : 0 < target) (hb : ∀ i ∈ cuts, 0 ≤ base i ∧ base i < target) :
    ∀ᶠ h : ℕ in atTop, ∑ i ∈ cuts, weight i * base i ^ h < target ^ h := by
  simpa only [one_mul] using eventually_weighted_pow_lt cuts weight base target 1 ht zero_lt_one hb

/-- A fixed finite collection of cuts whose base-two exponents are all strictly
smaller than `L` cannot account for growth of `(2 ^ L) ^ h` at unbounded powers. -/
theorem balancedGrowth_threshold (cuts : Finset ι) (weight exponent : ι → ℝ) (L : ℝ)
    (gap : ∀ i ∈ cuts, exponent i < L) :
    ∃ N : ℕ, ∀ h ≥ N, ∑ i ∈ cuts, weight i * ((2 : ℝ) ^ exponent i) ^ h < ((2 : ℝ) ^ L) ^ h := by
  have h := eventually_weighted_pow_lt_target cuts weight (fun i => (2 : ℝ) ^ exponent i)
    ((2 : ℝ) ^ L) (by positivity) (fun i hi =>
      ⟨by positivity, Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (gap i hi)⟩)
  exact eventually_atTop.mp h

end VPVNP
end Computability
end OAI

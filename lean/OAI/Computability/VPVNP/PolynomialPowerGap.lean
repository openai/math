import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Polynomial losses in a finite sum of tensor powers

The cut bounds in §4.2 of *VP and VNP differ over every field* have bases strictly
smaller than the target spectral value. A polynomially growing multiplicity of
terms across each cut preserves the eventual strict inequality.
-/

namespace OAI
namespace Computability
namespace VPVNP

open Filter Topology

/-- A fixed polynomial factor times a finite sum of powers with smaller bases is
eventually strictly smaller than the target power. -/
theorem eventually_polynomial_weighted_pow_lt_target {ι : Type*} (cuts : Finset ι)
    (weight base : ι → ℝ) (target : ℝ) (E : ℕ) (ht : 0 < target)
    (hw : ∀ i ∈ cuts, 0 ≤ weight i) (hb : ∀ i ∈ cuts, 0 ≤ base i ∧ base i < target) :
    ∀ᶠ h : ℕ in atTop, ((h : ℝ) + 2) ^ E * (∑ i ∈ cuts, weight i * base i ^ h) < target ^ h := by
  have hi (i : ι) (hic : i ∈ cuts) : Tendsto (fun h : ℕ ↦
      (3 ^ E * weight i) * ((h : ℝ) ^ E * (base i / target) ^ h)) atTop (𝓝 0) := by
    have lower := div_nonneg (hb i hic).1 ht.le
    have upper := (div_lt_one ht).mpr (hb i hic).2
    simpa using (tendsto_pow_const_mul_const_pow_of_lt_one E lower upper).const_mul
      (3 ^ E * weight i)
  have hlim : Tendsto (fun h : ℕ ↦ ∑ i ∈ cuts,
      (3 ^ E * weight i) * ((h : ℝ) ^ E * (base i / target) ^ h)) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum cuts hi
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlim.eventually_lt_const zero_lt_one] with h hh hlt
  have hone : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hshift : (h : ℝ) + 2 ≤ 3 * h := by linarith
  have hsum : 0 ≤ ∑ i ∈ cuts, weight i * base i ^ h :=
    Finset.sum_nonneg fun i hic ↦ mul_nonneg (hw i hic) (pow_nonneg (hb i hic).1 h)
  refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hshift E) hsum).trans_lt ?_
  apply (div_lt_one (pow_pos ht h)).mp
  calc
    (3 * (h : ℝ)) ^ E * (∑ i ∈ cuts, weight i * base i ^ h) / target ^ h =
        ∑ i ∈ cuts, (3 * (h : ℝ)) ^ E * (weight i * base i ^ h) / target ^ h := by
          simp only [Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
    _ = ∑ i ∈ cuts, (3 ^ E * weight i) * ((h : ℝ) ^ E * (base i / target) ^ h) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [div_pow, mul_pow]
      ring
    _ < 1 := hlt

end VPVNP
end Computability
end OAI

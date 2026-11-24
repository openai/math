import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IsLUB
import Mathlib.Tactic.Linarith

/-!
# Growth of contractions of a powered star

Section 2.3 of *VP and VNP differ over every field* computes the exponential
rate of the supremum of the values of contractions at a new party. A tensor
with local widths indexed by `h` fits into `u*m` copies of the width profile
exactly `u*m/h` times, using natural-number division.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Spectral

open Filter Topology

/-- The fraction of the power occupied by copies of a fixed witness has the
limit used in the star construction. -/
private theorem packedCopyRatio_tendsto (u h : ℕ) :
    Tendsto (fun m : ℕ ↦ ((u * m / h : ℕ) : ℝ) / m) atTop (𝓝 ((u : ℝ) / h)) := by
  have lim := (tendsto_nat_floor_mul_div_atTop
    (show 0 ≤ (u : ℝ) / h by positivity)).comp tendsto_natCast_atTop_atTop
  apply lim.congr
  intro m
  change (⌊(u : ℝ) / h * m⌋₊ : ℝ) / m = _
  rw [div_mul_eq_mul_div, ← Nat.cast_mul, Nat.floor_div_eq_div]

/-- Taking roots in the value of a single packed witness. -/
private theorem packedStarRoot_tendsto {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (u h : ℕ) :
    Tendsto (fun m : ℕ ↦ (a ^ m * b ^ (u*m/h)) ^ (m⁻¹ : ℝ)) atTop
      (𝓝 (a * b ^ ((u : ℝ) / h))) := by
  have lim := ((Real.continuousAt_const_rpow hb.ne').tendsto.comp
    (packedCopyRatio_tendsto u h)).const_mul a
  apply lim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  change a * b ^ (((u * m / h : ℕ) : ℝ) / m) = _
  rw [Real.mul_rpow (pow_nonneg ha m) (pow_nonneg hb.le _),
    Real.pow_rpow_inv_natCast ha hm.ne', ← Real.rpow_natCast b (u*m/h),
    ← Real.rpow_mul hb.le, div_eq_mul_inv]

/-- In the star case of Theorem 2.4, `I` indexes the pairs of a positive
width parameter and a nonzero old tensor of that width. `g` is the supremum
of their normalized log values, `a` is the old factor's value, and `C m` is
the supremum of the contracted values of the monomial's `m`-th power.
The packing and contraction inequalities imply the claimed root limit, even
for zero star multiplicity. -/
theorem starContractionRoot_tendsto {I : Type*} [Nonempty I] (height : I → ℕ)
    (value : I → ℝ) (u : ℕ) {a g : ℝ} (C : ℕ → ℝ)
    (ha : 0 ≤ a) (hv : ∀ i, 0 < value i)
    (hg : IsLUB (Set.range (fun i ↦ Real.logb 2 (value i) / height i)) g)
    (pack : ∀ i m, 0 < m → a ^ m * value i ^ (u * m / height i) ≤ C m)
    (bound : ∀ m, 0 < m → C m ≤ (a * (2 : ℝ) ^ ((u : ℝ) * g)) ^ m) :
    Tendsto (fun m : ℕ ↦ C m ^ (m⁻¹ : ℝ)) atTop (𝓝 (a * (2 : ℝ) ^ ((u : ℝ) * g))) := by
  obtain ⟨r, _, _, hr, hmem⟩ := hg.exists_seq_monotone_tendsto (Set.range_nonempty _)
  have htarget : Tendsto (fun n : ℕ ↦ a * (2 : ℝ) ^ ((u : ℝ) * r n)) atTop
      (𝓝 (a * (2 : ℝ) ^ ((u : ℝ) * g))) :=
    ((Real.continuousAt_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp
      (hr.const_mul (u : ℝ))).const_mul a
  apply tendsto_order.2
  constructor
  · intro x hx
    obtain ⟨n, hn⟩ := (htarget.eventually (lt_mem_nhds hx)).exists
    obtain ⟨i, hi⟩ := hmem n
    change x < a * (2 : ℝ) ^ ((u : ℝ) * r n) at hn
    rw [← hi, show (u : ℝ) * (Real.logb 2 (value i) / height i) =
      Real.logb 2 (value i) * ((u : ℝ) / height i) by ring,
      Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (hv i)] at hn
    filter_upwards [(packedStarRoot_tendsto ha (hv i) u (height i)).eventually (lt_mem_nhds hn),
      eventually_gt_atTop (0 : ℕ)] with m hx hm
    exact hx.trans_le (Real.rpow_le_rpow (mul_nonneg (pow_nonneg ha _) (pow_nonneg (hv i).le _))
      (pack i m hm) (by positivity))
  · intro x hx
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    have i := Classical.choice ‹Nonempty I›
    have hc : 0 ≤ C m := (mul_nonneg (pow_nonneg ha _) (pow_nonneg (hv i).le _)).trans
      (pack i m hm)
    have h := Real.rpow_le_rpow hc (bound m hm) (show 0 ≤ (m⁻¹ : ℝ) by positivity)
    rw [Real.pow_rpow_inv_natCast (mul_nonneg ha (by positivity)) hm.ne'] at h
    exact h.trans_lt hx

/-- A positive contraction supremum admits a contraction strictly above half its value. -/
theorem exists_gt_half_of_isLUB {S : Set ℝ} {c : ℝ} (h : IsLUB S c) (hc : 0 < c) :
    ∃ d ∈ S, c / 2 < d ∧ d ≤ c :=
  h.exists_between (by linarith)

/-- Any fixed multiplicative loss disappears after taking the `m`-th root. It is
sufficient for the power estimate to hold on an unbounded set of integers. -/
theorem limit_le_of_half_power_bound {C : ℕ → ℝ} {L B K f : ℝ}
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hK : 0 < K)
    (hC : ∀ᶠ m in atTop, 0 ≤ C m)
    (hlim : Tendsto (fun m : ℕ ↦ C m ^ (m : ℝ)⁻¹) atTop (𝓝 f))
    (hbound : ∃ᶠ m in atTop, L ^ m * (C m / 2) ≤ K * B ^ m) : L * f ≤ B := by
  have hrec : Tendsto (fun m : ℕ ↦ (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h2K : 0 < 2 * K := by positivity
  have hscale : Tendsto (fun m : ℕ ↦ (2 * K) ^ (m : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa only [Real.rpow_zero] using tendsto_const_nhds.rpow hrec (Or.inl h2K.ne')
  have hright : Tendsto (fun m : ℕ ↦ (2 * K) ^ (m : ℝ)⁻¹ * B) atTop (𝓝 B) := by
    simpa only [one_mul] using hscale.mul_const B
  apply le_of_tendsto_of_tendsto_of_frequently (hlim.const_mul L) hright
  apply (hbound.and_eventually (hC.and (eventually_gt_atTop (0 : ℕ)))).mono
  rintro m ⟨hm, hCm, hpos⟩
  have hprod : L ^ m * C m ≤ (2 * K) * B ^ m := by linarith
  have hroot := Real.rpow_le_rpow (mul_nonneg (pow_nonneg hL m) hCm) hprod
    (inv_nonneg.mpr (Nat.cast_nonneg m : 0 ≤ (m : ℝ)))
  simpa only [Real.mul_rpow (pow_nonneg hL m) hCm,
    Real.mul_rpow h2K.le (pow_nonneg hB m), Real.pow_rpow_inv_natCast hL hpos.ne',
    Real.pow_rpow_inv_natCast hB hpos.ne'] using hroot

end Spectral

end VPVNP
end Computability
end OAI

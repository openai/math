import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Sum

/-!
# Additivity under subparty normalization

The direct-sum expansion on a subset of parties in Lemma 2.3 of *VP and VNP
differ over every field* has `m + 1` binomial groups. Bounding each group by
the whole expansion and the whole expansion by the sum of group values
suffices to recover exact additivity after normalizing by the diagonal
exponent.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Spectral

open Filter Topology

/-- The number of binomial groups has exponential growth rate one. -/
private theorem tendsto_binomialGroupCount_root :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ (n : ℝ)⁻¹) atTop (𝓝 1) := by
  have lim := (tendsto_rpow_div_mul_add 1 1 (-1) zero_ne_one).comp
    (tendsto_atTop_add_const_right (atTop : Filter ℕ) (1 : ℝ) tendsto_natCast_atTop_atTop)
  simpa only [Function.comp_def, one_mul, add_neg_cancel_right, one_div] using lim

/-- A factor `m + 1` in a comparison of all powers disappears in the growth rate. -/
private theorem le_of_binomialGroupCount_pow_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ∀ m : ℕ, 0 < m → x ^ m ≤ ((m : ℝ) + 1) * y ^ m) : x ≤ y := by
  have lim : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ (n : ℝ)⁻¹ * y) atTop (𝓝 y) := by
    simpa only [one_mul] using tendsto_binomialGroupCount_root.mul_const y
  apply ge_of_tendsto lim
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  have := Real.rpow_le_rpow (pow_nonneg hx m) (h m hm) (show 0 ≤ (m : ℝ)⁻¹ by positivity)
  simpa only [Real.mul_rpow (show 0 ≤ (m : ℝ) + 1 by positivity) (pow_nonneg hy m),
    Real.pow_rpow_inv_natCast hx hm.ne', Real.pow_rpow_inv_natCast hy hm.ne'] using this

/-- Lemma 2.3's binomial-group bounds imply additivity of the normalized
value. `h` is the positive exponent of the embedded local diagonal, `a` and
`b` are the normalized values of two tensors, and `z` is the normalized
value of their direct sum. -/
theorem normalizedAdditivity_of_binomialBounds {a b z h : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : 0 ≤ z) (hh : 0 < h)
    (group_le : ∀ m j : ℕ, 0 < m → j ≤ m →
      (a ^ j * b ^ (m - j) * m.choose j) ^ h ≤ (z ^ m) ^ h)
    (expansion_le : ∀ m : ℕ, 0 < m → (z ^ m) ^ h ≤
      ∑ j ∈ Finset.range (m + 1), (a ^ j * b ^ (m - j) * m.choose j) ^ h) :
    z = a + b := by
  let A (m j : ℕ) := a ^ j * b ^ (m - j) * m.choose j
  have hA (m j : ℕ) : 0 ≤ A m j := by dsimp [A]; positivity
  have sumA (m : ℕ) : ∑ j ∈ Finset.range (m + 1), A m j = (a + b)^m := (add_pow a b m).symm
  have constSum (m : ℕ) (c : ℝ) :
      ∑ _j ∈ Finset.range (m + 1), c = ((m : ℝ) + 1) * c := by simp
  apply le_antisymm
  · apply (Real.rpow_le_rpow_iff hz (add_nonneg ha hb) hh).mp
    apply le_of_binomialGroupCount_pow_le (Real.rpow_nonneg hz _)
      (Real.rpow_nonneg (add_nonneg ha hb) _)
    intro m hm
    calc
      (z ^ h) ^ m = (z ^ m) ^ h := by
        rw [← Real.rpow_natCast_mul hz, mul_comm (m : ℝ), Real.rpow_mul_natCast hz]
      _ ≤ ∑ j ∈ Finset.range (m + 1), A m j ^ h := expansion_le m hm
      _ ≤ ∑ _j ∈ Finset.range (m + 1), ((a + b)^m) ^ h := by
        apply Finset.sum_le_sum
        intro j hj
        apply Real.rpow_le_rpow (hA m j) _ hh.le
        rw [← sumA m]
        exact Finset.single_le_sum (fun k _ ↦ hA m k) hj
      _ = ((m : ℝ) + 1) * ((a + b) ^ h) ^ m := by
        rw [constSum, ← Real.rpow_natCast_mul (add_nonneg ha hb), mul_comm (m : ℝ),
          Real.rpow_mul_natCast (add_nonneg ha hb)]
  · apply le_of_binomialGroupCount_pow_le (add_nonneg ha hb) hz
    intro m hm
    rw [← sumA, ← constSum]
    apply Finset.sum_le_sum
    intro j hj
    exact (Real.rpow_le_rpow_iff (hA m j) (pow_nonneg hz _) hh).mp
      (group_le m j hm (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))

private theorem subadditive_sum_le {S : Type*} [CommSemiring S] (f : S →*₀ ℝ)
    (hadd : ∀ x y, f (x + y) ≤ f x + f y) {ι : Type*} (s : Finset ι) (t : ι → S) :
    f (∑ i ∈ s, t i) ≤ ∑ i ∈ s, f (t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (hadd _ _).trans (add_le_add_right ih _)

/-- The numerical bounds of Lemma 2.3 follow from the semiring binomial
expansion. The embedded tensor value is multiplicative, subadditive on
direct sums, and monotone under projection onto either direct summand. -/
theorem normalized_multiplicative_value_add {S : Type*} [CommSemiring S] (f : S →*₀ ℝ)
    (hf : ∀ x, 0 ≤ f x) (hsummand : ∀ x y, f x ≤ f (x + y))
    (hadd : ∀ x y, f (x + y) ≤ f x + f y) {h : ℝ} (hh : 0 < h)
    (hdiag : ∀ n : ℕ, f n = (n : ℝ) ^ h) (x y : S) :
    f (x + y) ^ h⁻¹ = f x ^ h⁻¹ + f y ^ h⁻¹ := by
  let term (m j : ℕ) := x ^ j * y ^ (m - j) * m.choose j
  have hx := hf x
  have hy := hf y
  have groupValue (m j : ℕ) :
      ((f x ^ h⁻¹) ^ j * (f y ^ h⁻¹) ^ (m - j) * m.choose j) ^ h = f (term m j) := by
    dsimp only [term]
    rw [map_mul, map_mul, map_pow, map_pow, hdiag]
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast_mul (Real.rpow_nonneg (hf _) _),
      ← Real.rpow_natCast_mul (Real.rpow_nonneg (hf _) _),
      ← Real.rpow_mul (hf x), ← Real.rpow_mul (hf y)]
    have cancel (n : ℕ) : h⁻¹ * ((n : ℝ) * h) = n := by field_simp
    rw [cancel, cancel, Real.rpow_natCast, Real.rpow_natCast]
  have totalValue (m : ℕ) : ((f (x + y) ^ h⁻¹) ^ m) ^ h = f ((x + y) ^ m) := by
    rw [map_pow, ← Real.rpow_natCast_mul (Real.rpow_nonneg (hf _) _), ← Real.rpow_mul (hf _),
      show h⁻¹ * ((m : ℝ) * h) = m by field_simp, Real.rpow_natCast]
  apply normalizedAdditivity_of_binomialBounds (Real.rpow_nonneg (hf x) _)
    (Real.rpow_nonneg (hf y) _) (Real.rpow_nonneg (hf _) _) hh
  · intro m j _ hj
    rw [groupValue, totalValue, add_pow]
    change f (term m j) ≤ f (∑ i ∈ Finset.range (m + 1), term m i)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))]
    exact hsummand _ _
  · intro m _
    simp only [groupValue, totalValue, add_pow]
    exact subadditive_sum_le f hadd _ _

end Spectral

end VPVNP
end Computability
end OAI

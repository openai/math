import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

/-! Bounds on the intermediate coefficients and integer rows during LLL size reduction. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A quotient of positive bounded integral Gram determinants controls a Gram–Schmidt
length and its reciprocal. The relation is expressed without division. -/
theorem gram_length_and_inverse_le {g A D K : ℝ} (hg : 0 < g) (hA : 1 ≤ A)
    (hD : 1 ≤ D) (hAK : A ≤ K) (hDK : D ≤ K) (hGram : g^2 * D = A) :
    g ≤ K ∧ g⁻¹ ≤ K := by
  have hK : 1 ≤ K := hA.trans hAK
  have hKpos : 0 ≤ K := by linarith
  have hgsq : g ^ 2 ≤ K := by
    have h := mul_le_mul_of_nonneg_left hD (sq_nonneg g)
    nlinarith
  have hKsq : K ≤ K ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hK hKpos]
  have hgK : 1 ≤ (g*K)^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hDK (sq_nonneg g),
      mul_le_mul_of_nonneg_left hKsq (sq_nonneg g)]
  constructor
  · nlinarith [sq_nonneg (g-K)]
  · rw [inv_le_iff_one_le_mul₀ hg]
    by_contra! h
    have hn := mul_nonneg hg.le hKpos
    nlinarith [mul_pos (sub_pos.mpr h) (show 0 < 1 + g*K by linarith)]

/-- Actual rounded Gram–Schmidt coefficient used in a size reduction. -/
noncomputable def roundedCoefficient (x w : E) : ℤ := round (inner ℝ w x / ‖w‖ ^ 2)

/-- A Gram–Schmidt coefficient is bounded by the row norm times the reciprocal
orthogonal length. This estimate also applies to tie-breaking choices in native reduction. -/
theorem gramCoefficient_bound (x w : E) {K : ℝ} (hK : 0 ≤ K) (hw : ‖w‖⁻¹ ≤ K) :
    |inner ℝ w x / ‖w‖ ^ 2| ≤ K * ‖x‖ := by
  let μ := inner ℝ w x / ‖w‖ ^ 2
  change |μ| ≤ _
  by_cases h : w = 0
  · simp [μ, h, mul_nonneg hK (norm_nonneg x)]
  have hn := norm_pos_iff.mpr h
  rw [show |μ| = |inner ℝ w x| / ‖w‖ ^ 2 from by simp [μ, abs_div]]
  calc
    _ ≤ (‖w‖ * ‖x‖) / ‖w‖ ^ 2 :=
      div_le_div_of_nonneg_right (abs_real_inner_le_norm w x) (sq_nonneg _)
    _ = ‖w‖⁻¹ * ‖x‖ := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hw (norm_nonneg x)

theorem nearbyIntegerCoefficient_bound (x w : E) (r : ℤ) {K : ℝ}
    (hK : 0 ≤ K) (hw : ‖w‖⁻¹ ≤ K)
    (hr : |inner ℝ w x / ‖w‖ ^ 2 - (r : ℝ)| ≤ 1 / 2) :
    |(r : ℝ)| ≤ K * ‖x‖ + 1 := by
  let μ := inner ℝ w x / ‖w‖ ^ 2
  calc
    |(r : ℝ)| = |μ - (μ - r)| := by ring_nf
    _ ≤ |μ| + |μ - r| := abs_sub ..
    _ ≤ K * ‖x‖ + 1 := add_le_add (gramCoefficient_bound x w hK hw) (hr.trans (by norm_num))

theorem roundedCoefficient_bound (x w : E) {K : ℝ} (hK : 0 ≤ K) (hw : ‖w‖⁻¹ ≤ K) :
    |(roundedCoefficient x w : ℝ)| ≤ K * ‖x‖ + 1 :=
  nearbyIntegerCoefficient_bound x w _ hK hw (abs_sub_round _)

/-- Subtract the rounded integer multiple of a previously reduced row. -/
noncomputable def reduceByRow (x : E) (r : E × E) : E :=
  x - (roundedCoefficient x r.2 : ℝ) • r.1

theorem sub_integer_row_growth (x b : E) (r : ℤ) {B K : ℝ} (hK : 0 ≤ K)
    (hb : ‖b‖ ≤ B) (hr : |(r : ℝ)| ≤ K * ‖x‖ + 1) :
    ‖x - (r : ℝ) • b‖ + 1 ≤ (1 + (K+1)*B) * (‖x‖+1) := by
  have h' : |(r : ℝ)| ≤ (K+1) * (‖x‖+1) := by nlinarith [norm_nonneg x]
  calc
    _ ≤ ‖x‖ + |(r : ℝ)| * ‖b‖ + 1 := by
      simpa only [norm_smul, Real.norm_eq_abs] using
        add_le_add_left (norm_sub_le x ((r : ℝ) • b)) 1
    _ ≤ ‖x‖ + (K+1) * (‖x‖+1) * B + 1 := by
      have := mul_le_mul h' hb (norm_nonneg _) (by positivity)
      linarith
    _ = _ := by ring

theorem reduceByRow_bound (x : E) (r : E × E) {B K : ℝ} (hK : 0 ≤ K)
    (hr : ‖r.1‖ ≤ B) (hg : ‖r.2‖⁻¹ ≤ K) :
    ‖reduceByRow x r‖ + 1 ≤ (1 + (K+1)*B) * (‖x‖+1) :=
  sub_integer_row_growth x r.1 _ hK hr (roundedCoefficient_bound x r.2 hK hg)

/-- Each prefix of a size-reduction pass can be substituted for `rows`, so the same
single exponential bounds every temporary row, even before it is fully reduced. -/
theorem sizeReductionPass_bound (x : E) (rows : List (E × E)) {B K : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hr : ∀ r ∈ rows, ‖r.1‖ ≤ B ∧ ‖r.2‖⁻¹ ≤ K) :
    ‖rows.foldl reduceByRow x‖ + 1 ≤ (1 + (K+1)*B) ^ rows.length * (‖x‖+1) := by
  induction rows generalizing x with
  | nil => simp
  | cons r rs ih =>
    have hrow := hr r (by simp)
    have htail := ih (reduceByRow x r) (fun r' hmem => hr r' (by simp [hmem]))
    calc
      _ ≤ _ := htail
      _ ≤ (1 + (K+1)*B)^rs.length * ((1 + (K+1)*B)*(‖x‖+1)) :=
        mul_le_mul_of_nonneg_left (reduceByRow_bound x r hK hrow.1 hrow.2)
          (pow_nonneg (add_nonneg (by norm_num) (mul_nonneg (by positivity) hB)) _)
      _ = _ := by simp [pow_succ]; ring


/-- If the row and reciprocal Gram-length bounds have at most `L` bits, the
binary size grows by at most `2*L+2` per individual reduction. -/
theorem sizeReductionPass_bit_bound (x : E) (rows : List (E × E)) {L : ℕ}
    (hx : ‖x‖ + 1 ≤ (2 : ℝ)^L)
    (hr : ∀ r ∈ rows, ‖r.1‖ ≤ (2 : ℝ)^L ∧ ‖r.2‖⁻¹ ≤ (2 : ℝ)^L) :
    ‖rows.foldl reduceByRow x‖ + 1 ≤ (2 : ℝ)^((2*L + 2)*rows.length + L) := by
  let K := (2 : ℝ)^L
  have hK : (1 : ℝ) ≤ K := one_le_pow₀ (by norm_num)
  have hK0 : 0 ≤ K := by linarith
  have hfactor : 1 + (K+1)*K ≤ (2 : ℝ)^(2*L+2) := by
    rw [pow_add, two_mul, pow_add]
    change 1 + (K+1)*K ≤ (K*K)*(2:ℝ)^2
    nlinarith [sq_nonneg (K-1)]
  calc
    _ ≤ (1+(K+1)*K)^rows.length * (‖x‖+1) :=
      sizeReductionPass_bound x rows hK0 hK0 hr
    _ ≤ ((2 : ℝ)^(2*L+2))^rows.length * (2:ℝ)^L :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hfactor _) hx
        (by positivity) (by positivity)
    _ = _ := by rw [pow_add (2 : ℝ) ((2*L+2)*rows.length) L, pow_mul (2 : ℝ) (2*L+2) rows.length]

end Lattice
end LinearProgramming
end Optimization
end OAI

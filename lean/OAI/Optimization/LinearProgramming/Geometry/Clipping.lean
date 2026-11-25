import OAI.Optimization.LinearProgramming.Compression.Basic
import OAI.Optimization.LinearProgramming.Geometry.Circuits
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Basic.Sign.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-! # Stability of orthogonality under compression of minor logarithms -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open scoped BigOperators

/-- Truncate a base-two logarithm to the interval `[-B,B]`. -/
def clipLog (B x : ℝ) : ℝ := max (-B) (min x B)

private lemma rpow_two_sub_le {a b : ℝ} (hab : a ≤ b) (ha : a ≤ 1) (hd : b - a ≤ 1) :
    (2 : ℝ) ^ b - 2 ^ a ≤ 2 * (b - a) := by
  have hbase : (2 : ℝ) ^ a ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha
  have hstep : (2 : ℝ) ^ (b - a) ≤ 1 + (b - a) := by
    simpa only [one_add_one_eq_two, mul_one] using
      rpow_one_add_le_one_add_mul_self (s := 1) (by norm_num) (sub_nonneg.mpr hab) hd
  calc
    (2 : ℝ) ^ b - 2 ^ a = 2 ^ a * (2 ^ (b - a) - 1) := by
      rw [mul_sub, ← Real.rpow_add (by norm_num : 0 < (2 : ℝ)), add_sub_cancel, mul_one]
    _ ≤ 2 ^ a * (b - a) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg (by norm_num) _)
    _ ≤ 2 * (b - a) := mul_le_mul_of_nonneg_right hbase (sub_nonneg.mpr hab)

private lemma abs_rpow_two_sub_le {a b d : ℝ} (ha : a ≤ 1) (hb : b ≤ 1)
    (hd : d ≤ 1) (h : |a - b| ≤ d) : |(2 : ℝ) ^ a - 2 ^ b| ≤ 2 * d := by
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr hab), neg_sub] at h
    rw [abs_of_nonpos (sub_nonpos.mpr
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hab)), neg_sub]
    linarith [rpow_two_sub_le hab ha (h.trans hd)]
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)] at h
    rw [abs_of_nonneg (sub_nonneg.mpr
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hba))]
    linarith [rpow_two_sub_le hba hb (h.trans hd)]

private lemma clipLog_rpow_error {B x : ℝ} (hx : x ≤ B) :
    |(2 : ℝ) ^ x - 2 ^ (clipLog B x)| ≤ 2 ^ (-B) := by
  rw [clipLog, min_eq_left hx]
  rcases le_total (-B) x with hlo | hlo
  · rw [max_eq_right hlo, sub_self, abs_zero]
    positivity
  · rw [max_eq_left hlo, abs_of_nonpos (sub_nonpos.mpr
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hlo))]
    linarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) x]

/-- A clipped comparison accurate to `2⁻ᴮ` controls the error of the positive
magnitude ratio, even if either logarithm lies below the clipping threshold. -/
theorem rpow_error_of_clipped_log {B v w : ℝ} (hB : 2 ≤ B) (hv : v ≤ 0)
    (hclip : |clipLog B w - clipLog B v| ≤ (2 : ℝ) ^ (-B)) :
    |(2 : ℝ) ^ w - 2 ^ v| ≤ 8 * 2 ^ (-B) := by
  let d := (2 : ℝ) ^ (-B)
  have hd₀ : 0 ≤ d := Real.rpow_nonneg (by norm_num) _
  have hd₁ : d ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hcv : clipLog B v ≤ 0 := max_le (by linarith) ((min_le_left _ _).trans hv)
  have hcw : clipLog B w ≤ d := by
    have h := (abs_le.mp hclip).2
    linarith
  have hw : w ≤ B := by
    by_contra! h
    have : B ≤ clipLog B w := by
      unfold clipLog
      rw [min_eq_right h.le]
      exact le_max_right _ _
    linarith
  have he := abs_rpow_two_sub_le (hcw.trans hd₁) (hcv.trans (by norm_num)) hd₁ hclip
  have hw' := clipLog_rpow_error hw
  have hv' := clipLog_rpow_error (hv.trans (by linarith : 0 ≤ B))
  have first := abs_sub_le ((2 : ℝ)^w) (2 ^ clipLog B w) (2 ^ clipLog B v)
  have second := abs_sub_le ((2 : ℝ)^w) (2 ^ clipLog B v) (2 ^ v)
  rw [abs_sub_comm ((2 : ℝ) ^ v)] at hv'
  change |(2 : ℝ)^w - 2 ^ v| ≤ 8 * d
  linarith


/-- Summing the errors relative to a largest nonzero original product.
The coefficients are the signs of the coordinate products (zero on missing
minors). The common factor is the product of the two normalization factors. -/
theorem almostOrthogonal_of_clipped_ratios {ι : Type*} [Fintype ι]
    (orig compressed sign : ι → ℝ) (B scale : ℝ) (hB : 2 ≤ B) (hscale : 0 ≤ scale)
    (hsign : ∀ i, |sign i| ≤ 1)
    (horth : ∑ i, sign i * (2 : ℝ) ^ orig i = 0)
    (hnorm : ∀ i, sign i ≠ 0 → scale * 2 ^ compressed i ≤ 1)
    (hclip : ∀ i j, sign i ≠ 0 → sign j ≠ 0 →
      |clipLog B (compressed i - compressed j) - clipLog B (orig i - orig j)| ≤
        (2 : ℝ) ^ (-B)) :
    |∑ i, sign i * (scale * (2 : ℝ) ^ compressed i)| ≤
      8 * Fintype.card ι * (2 : ℝ) ^ (-B) := by
  classical
  let s := Finset.univ.filter fun i => sign i ≠ 0
  by_cases hs : s.Nonempty
  · obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image s orig hs
    have hj0 : sign j ≠ 0 := (Finset.mem_filter.mp hj).2
    let c := scale * 2 ^ compressed j
    have hc : 0 ≤ c := mul_nonneg hscale (Real.rpow_nonneg (by norm_num) _)
    have hc' : c ≤ 1 := hnorm j hj0
    let e (i : ι) := c * (sign i * ((2 : ℝ)^(compressed i - compressed j) -
      2 ^ (orig i - orig j)))
    have he (i : ι) : |e i| ≤ 8 * 2 ^ (-B) := by
      by_cases hi : sign i = 0
      · simp only [e, hi, zero_mul, mul_zero, abs_zero]
        positivity
      · have hv : orig i - orig j ≤ 0 :=
          sub_nonpos.mpr (hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
        have h := rpow_error_of_clipped_log hB hv (hclip i j hi hj0)
        calc
          |e i| = c * (|sign i| * |(2 : ℝ) ^ (compressed i - compressed j) -
              2 ^ (orig i - orig j)|) := by simp only [e, abs_mul, abs_of_nonneg hc]
          _ ≤ 1 * (1 * (8 * 2 ^ (-B))) := by gcongr; exact hsign i
          _ = 8 * 2 ^ (-B) := by ring
    have hzero : ∑ i, sign i * (2 : ℝ)^(orig i - orig j) = 0 := by
      simp_rw [Real.rpow_sub (by norm_num : 0 < (2 : ℝ)), ← mul_div_assoc]
      rw [← Finset.sum_div, horth, zero_div]
    have hrep (i : ι) : sign i * (scale * (2 : ℝ)^compressed i) =
        e i + c * (sign i * 2 ^ (orig i - orig j)) := by
      have hpow : (2 : ℝ)^compressed j * 2 ^ (compressed i - compressed j) =
          2 ^ compressed i := by
        rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ)), add_sub_cancel]
      dsimp only [e, c]
      linear_combination sign i * scale * (-hpow)
    calc
      |∑ i, sign i * (scale * (2 : ℝ) ^ compressed i)| = |∑ i, e i| := by
        simp_rw [hrep]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum Finset.univ (fun i => sign i * (2 : ℝ) ^ (orig i - orig j)) c, hzero, mul_zero, add_zero]
      _ ≤ ∑ i, |e i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : ι, 8 * (2 : ℝ) ^ (-B) := Finset.sum_le_sum (fun i _ => he i)
      _ = 8 * Fintype.card ι * (2 : ℝ) ^ (-B) := by simp; ring
  · have hall (i : ι) : sign i = 0 := by
      by_contra hi
      exact hs ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    simp only [hall, zero_mul, Finset.sum_const_zero, abs_zero]
    positivity

/-- Four clipped minor log terms suffice in each comparison. The maps `u` and
`v` name the primal and dual minor factors of each nonzero product. The same
minor may occur several times. -/
theorem almostOrthogonal_of_fourTermClip {ι κ : Type*} [Fintype ι]
    (u v : ι → κ) (ell f : κ → ℝ) (sign : ι → ℝ) (B scale : ℝ)
    (hB : 2 ≤ B) (hscale : 0 ≤ scale) (hsign : ∀ i, |sign i| ≤ 1)
    (horth : ∑ i, sign i * (2 : ℝ) ^ (ell (u i) + ell (v i)) = 0)
    (hnorm : ∀ i, sign i ≠ 0 → scale * (2 : ℝ) ^ (f (u i) + f (v i)) ≤ 1)
    (hclip : ∀ a b c d : κ,
      |clipLog B ((f a + f b) - (f c + f d)) -
        clipLog B ((ell a + ell b) - (ell c + ell d))| ≤ (2 : ℝ) ^ (-B)) :
    |∑ i, sign i * (scale * (2 : ℝ) ^ (f (u i) + f (v i)))| ≤
      8 * Fintype.card ι * (2 : ℝ) ^ (-B) :=
  almostOrthogonal_of_clipped_ratios _ _ _ B scale hB hscale hsign horth hnorm
    (fun i j _ _ => hclip (u i) (v i) (u j) (v j))


open SignType

/-- Replace a nonzero minor by the signed power of two with its compressed
logarithm, then scale each coordinate by its price. Zeros retain their sign zero. -/
noncomputable def pricedMinorRow {ι : Type*} (row logMagnitude price : ι → ℝ) (i : ι) : ℝ :=
  (sign (row i) : ℝ) * (2 : ℝ) ^ (logMagnitude i - price i)

/-- The actual normalized vector, using the sup norm of the finite coordinate space. -/
noncomputable def normalizedMinorRow {ι : Type*} [Fintype ι]
    (row logMagnitude price : ι → ℝ) (i : ι) : ℝ :=
  ‖pricedMinorRow row logMagnitude price‖⁻¹ * pricedMinorRow row logMagnitude price i

theorem abs_normalizedMinorRow_le_one {ι : Type*} [Fintype ι]
    (row f t : ι → ℝ) (i : ι) : |normalizedMinorRow row f t i| ≤ 1 := by
  let a := pricedMinorRow row f t
  change |‖a‖⁻¹ * a i| ≤ 1
  rw [mul_comm, ← div_eq_mul_inv, abs_div, abs_of_nonneg (norm_nonneg _)]
  by_cases h : ‖a‖ = 0
  · simp [h]
  · apply (div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h))).2
    exact norm_le_pi_norm a i

private lemma signed_logb_reconstruct (x : ℝ) :
    (sign x : ℝ) * (2 : ℝ) ^ (Real.logb 2 |x|) = x := by
  by_cases h : x = 0
  · simp [h]
  · rw [Real.rpow_logb (by norm_num : 0 < (2 : ℝ)) (by norm_num : (2 : ℝ) ≠ 1)
        (abs_pos.mpr h), sign_mul_abs]

private lemma abs_coe_sign_bound (s : SignType) : |(s : ℝ)| ≤ 1 := by
  cases s <;> norm_num [SignType.cast]

private lemma abs_coe_sign_one (s : SignType) (h : (s : ℝ) ≠ 0) : |(s : ℝ)| = 1 := by
  cases s <;> norm_num [SignType.cast] at *

/-- Lemma 2.2 for actual orthogonal determinant vectors. The normalized
vectors are constructed by sign-preserving replacement, reciprocal price
scaling, and division by each resulting sup norm. The comparison hypotheses
need only cover pairs of nonzero coordinate products. -/
theorem almostOrthogonal_normalizedMinorRows {ι : Type*} [Fintype ι]
    (a b f g t : ι → ℝ) (B : ℝ) (hB : 2 ≤ B)
    (horth : ∑ i, a i * b i = 0)
    (hclip : ∀ i j, a i * b i ≠ 0 → a j * b j ≠ 0 →
      |clipLog B ((f i + g i) - (f j + g j)) -
        clipLog B ((Real.logb 2 |a i| + Real.logb 2 |b i|) -
          (Real.logb 2 |a j| + Real.logb 2 |b j|))| ≤ (2 : ℝ) ^ (-B)) :
    |∑ i, normalizedMinorRow a f t i * normalizedMinorRow b g (-t) i| ≤
      8 * Fintype.card ι * (2 : ℝ) ^ (-B) := by
  let σ (i : ι) : ℝ := sign (a i * b i)
  let scale := ‖pricedMinorRow a f t‖⁻¹ * ‖pricedMinorRow b g (-t)‖⁻¹
  have hscale : 0 ≤ scale := mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
    (inv_nonneg.mpr (norm_nonneg _))
  have hnonzero (i : ι) (h : σ i ≠ 0) : a i * b i ≠ 0 := by
    intro h'
    simp [σ, h'] at h
  have hprod (i : ι) : normalizedMinorRow a f t i * normalizedMinorRow b g (-t) i =
      σ i * (scale * (2 : ℝ) ^ (f i + g i)) := by
    have hpow : (2 : ℝ) ^ (f i + g i) = 2 ^ (f i - t i) * 2 ^ (g i - -t i) := by
      rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
      congr 1
      ring
    simp only [normalizedMinorRow, pricedMinorRow, Pi.neg_apply, σ, scale, sign_mul,
      SignType.coe_mul, hpow]
    ring
  have hnorm (i : ι) (hi : σ i ≠ 0) : scale * (2 : ℝ) ^ (f i + g i) ≤ 1 := by
    have h := mul_le_mul (abs_normalizedMinorRow_le_one a f t i)
      (abs_normalizedMinorRow_le_one b g (-t) i) (abs_nonneg _) zero_le_one
    rw [← abs_mul, hprod, abs_mul, abs_coe_sign_one (sign (a i * b i)) hi,
      abs_of_nonneg (mul_nonneg hscale (Real.rpow_nonneg (by norm_num) _)), one_mul, one_mul] at h
    exact h
  have horig (i : ι) : σ i * (2 : ℝ) ^ (Real.logb 2 |a i| + Real.logb 2 |b i|) =
      a i * b i := by
    rw [Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
    change (sign (a i * b i) : ℝ) * _ = _
    rw [sign_mul, SignType.coe_mul]
    calc
      _ = ((sign (a i) : ℝ) * 2 ^ Real.logb 2 |a i|) *
          ((sign (b i) : ℝ) * 2 ^ Real.logb 2 |b i|) := by ring
      _ = a i * b i := by rw [signed_logb_reconstruct, signed_logb_reconstruct]
  simp_rw [hprod]
  refine almostOrthogonal_of_clipped_ratios
    (fun i => Real.logb 2 |a i| + Real.logb 2 |b i|) (fun i => f i + g i) σ B scale
    hB hscale (fun i => abs_coe_sign_bound (sign (a i * b i))) ?_ hnorm ?_
  · simpa only [horig] using horth
  · exact fun i j hi hj => hclip i j (hnonzero i hi) (hnonzero j hj)


/-- Rounding either factor (or both) of each coordinate product changes
the dot product by at most the sum of the two coordinate errors, times the
dimension. One factor can be left exact by setting its error budget to zero. -/
theorem dotProduct_rounding_error {ι : Type*} [Fintype ι] (a b a' b' : ι → ℝ)
    (ea eb : ℝ) (ha : ∀ i, |a' i| ≤ 1) (hb : ∀ i, |b i| ≤ 1)
    (ha' : ∀ i, |a' i - a i| ≤ ea) (hb' : ∀ i, |b' i - b i| ≤ eb) :
    |(∑ i, a' i * b' i) - ∑ i, a i * b i| ≤ Fintype.card ι * (ea + eb) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |a' i * b' i - a i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : ι, (ea + eb) := by
      apply Finset.sum_le_sum
      intro i _
      have h : a' i * b' i - a i * b i = (a' i - a i) * b i + a' i * (b' i-b i) := by ring
      rw [h]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      exact add_le_add ((mul_le_mul_of_nonneg_left (hb i) (abs_nonneg _)).trans
        ((mul_one _).le.trans (ha' i))) ((mul_le_mul_of_nonneg_right (ha i) (abs_nonneg _)).trans
        ((one_mul _).le.trans (hb' i)))
    _ = _ := by simp [mul_add]

private theorem intForm_fourTerms {κ : Type*} [Fintype κ] (p q r s : κ) :
    ∃ a : κ → ℤ, (∑ i, |(a i : ℝ)|) ≤ 4 ∧ ∀ x : κ → ℝ,
      Compression.intForm a x = (x p + x q) - (x r + x s) := by
  classical
  let u (j i : κ) : ℤ := if i = j then 1 else 0
  have hu (j : κ) : ∑ i, |(u j i : ℝ)| = 1 := by simp [u, apply_ite]
  have he (j : κ) (x : κ → ℝ) : ∑ i, (u j i : ℝ) * x i = x j := by
    simp [u, apply_ite, ite_mul]
  let a (i : κ) := (u p i + u q i) - (u r i + u s i)
  refine ⟨a, ?_, fun x => ?_⟩
  · calc
      _ ≤ ∑ i, (|(u p i : ℝ)| + |(u q i : ℝ)| + (|(u r i : ℝ)| + |(u s i : ℝ)|)) := by
        apply Finset.sum_le_sum
        intro i _
        simp only [a, Int.cast_sub, Int.cast_add]
        exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
      _ = 4 := by simp only [Finset.sum_add_distrib, hu]; norm_num
  · simp only [Compression.intForm, a, Int.cast_sub, Int.cast_add, sub_mul, add_mul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, he]

/-- Specialize the compression theorem's integer forms to any two ratios
of products, including all coincidences of indices. -/
theorem fourTermClip_of_intForm {κ : Type*} [Fintype κ] (ell f : κ → ℝ) (B δ : ℝ)
    (h : ∀ a : κ → ℤ, (∑ i, |(a i : ℝ)|) ≤ 4 →
      |Compression.clip B (Compression.intForm a f) -
        Compression.clip B (Compression.intForm a ell)| ≤ δ) (p q r s : κ) :
    |clipLog B ((f p + f q) - (f r + f s)) -
      clipLog B ((ell p + ell q) - (ell r + ell s))| ≤ δ := by
  obtain ⟨a, ha, he⟩ := intForm_fourTerms p q r s
  simpa only [he, clipLog, Compression.clip] using h a ha


/-- Select the assigned logarithm only at existing nonzero minors. An
identically zero row needs no index in the table. -/
noncomputable def assignedMinorLogs {ι κ : Type*} (row : ι → ℝ)
    (index : ∀ i, row i ≠ 0 → κ) (f : κ → ℝ) (i : ι) : ℝ :=
  if h : row i ≠ 0 then f (index i h) else 0

/-- The full clipped four-term estimate for a pair of indexed minor rows.
Only the nonzero minors require supplied indices. -/
theorem almostOrthogonal_of_minor_assignment {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a b price : ι → ℝ) (u : ∀ i, a i ≠ 0 → κ) (v : ∀ i, b i ≠ 0 → κ)
    (ell f : κ → ℝ) (B : ℝ) (hB : 2 ≤ B) (horth : ∑ i, a i * b i = 0)
    (hu : ∀ i h, ell (u i h) = Real.logb 2 |a i|)
    (hv : ∀ i h, ell (v i h) = Real.logb 2 |b i|)
    (hclip : ∀ z : κ → ℤ, (∑ i, |(z i : ℝ)|) ≤ 4 →
      |Compression.clip B (Compression.intForm z f) -
        Compression.clip B (Compression.intForm z ell)| ≤ (2 : ℝ)^(-B)) :
    |∑ i, normalizedMinorRow a (assignedMinorLogs a u f) price i *
      normalizedMinorRow b (assignedMinorLogs b v f) (-price) i| ≤
      8 * Fintype.card ι * (2 : ℝ)^(-B) := by
  apply almostOrthogonal_normalizedMinorRows _ _ _ _ _ _ hB horth
  intro i j hi hj
  obtain ⟨hai, hbi⟩ := mul_ne_zero_iff.mp hi
  obtain ⟨haj, hbj⟩ := mul_ne_zero_iff.mp hj
  simpa only [assignedMinorLogs, dite_eq_left hai, dite_eq_left hbi, dite_eq_left haj, dite_eq_left hbj,
    hu, hv] using fourTermClip_of_intForm ell f B _ hclip (u i hai) (v i hbi) (u j haj) (v j hbj)

open Matrix in
/-- The manuscript's almost-orthogonality lemma for signed minors of any two
row prefixes of orthogonal matrices, including full circuit representatives. -/
theorem almostOrthogonal_circuitMinor {ι κ ρ σ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ρ] [Fintype σ] {k l : ℕ}
    (D : Matrix ρ ι ℝ) (E : Matrix σ ι ℝ) (hDE : D * E.transpose = 0)
    (dr : Fin (k + 1) → ρ) (er : Fin (l + 1) → σ) (J : Fin k → ι) (L : Fin l → ι)
    (u : ∀ i, circuitMinor (D.submatrix dr id) J i ≠ 0 → κ)
    (v : ∀ i, circuitMinor (E.submatrix er id) L i ≠ 0 → κ)
    (ell f : κ → ℝ) (price : ι → ℝ) (B : ℝ) (hB : 2 ≤ B)
    (hu : ∀ i h, ell (u i h) = Real.logb 2 |circuitMinor (D.submatrix dr id) J i|)
    (hv : ∀ i h, ell (v i h) = Real.logb 2 |circuitMinor (E.submatrix er id) L i|)
    (hclip : ∀ z : κ → ℤ, (∑ i, |(z i : ℝ)|) ≤ 4 →
      |Compression.clip B (Compression.intForm z f) -
        Compression.clip B (Compression.intForm z ell)| ≤ (2 : ℝ)^(-B)) :
    let a := circuitMinor (D.submatrix dr id) J
    let b := circuitMinor (E.submatrix er id) L
    |∑ i, normalizedMinorRow a (assignedMinorLogs a u f) price i *
      normalizedMinorRow b (assignedMinorLogs b v f) (-price) i| ≤
      8 * Fintype.card ι * (2 : ℝ)^(-B) :=
  almostOrthogonal_of_minor_assignment _ _ price u v ell f B hB
    (circuitMinor_dot_eq_zero D E hDE dr er J L) hu hv hclip

end Geometry
end LinearProgramming
end Optimization
end OAI

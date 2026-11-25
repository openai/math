import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Lemmas

/-! The rational series used to approximate small base-two logarithms in Section 3. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

/-- The first `M` terms of the odd expansion of the natural logarithm.
Specializing the field to the rationals gives the exact finite computation. -/
def logTruncation {K : Type*} [Field K] (z : K) (M : ℕ) : K :=
  2 * ∑ i ∈ Finset.range M,
    ((z - 1) / (z + 1)) ^ (2 * i + 1) / (2 * (i : K) + 1)

theorem cast_logTruncation (z : ℚ) (M : ℕ) :
    ((logTruncation z M : ℚ) : ℝ) = logTruncation (z : ℝ) M := by
  simp [logTruncation]

private theorem change_of_variable {z : ℝ} (hz : 1 ≤ z) :
    (1 + (z - 1) / (z + 1)) / (1 - (z - 1) / (z + 1)) = z := by
  have h₁ : z + 1 ≠ 0 := by linarith
  have h₂ : (z - 1) / (z + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  field_simp [h₁, show 1 - (z - 1) / (z + 1) ≠ 0 by linarith]
  ring

/-- Uniform error for the odd series on the entire reduced interval, including its endpoints. -/
theorem abs_log_sub_logTruncation {z : ℝ} (hz : 1 ≤ z) (hz' : z ≤ 2) (M : ℕ) :
    |Real.log z - logTruncation z M| ≤ (1 / 2 : ℝ) ^ M := by
  let x := (z - 1) / (z + 1)
  have hx₀ : 0 ≤ x := div_nonneg (by linarith) (by linarith)
  have hx₁ : x ≤ 1 / 3 := (div_le_iff₀ (by linarith : 0 < z + 1)).2 (by linarith)
  have hx : |x| < 1 := by rw [abs_of_nonneg hx₀]; linarith
  have H := Real.sum_range_sub_log_div_le hx M
  rw [show (1 + x) / (1 - x) = z from change_of_variable hz, abs_of_nonneg hx₀] at H
  have hx₂ : x ^ 2 ≤ 1 / 9 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx₁) (by linarith : 0 ≤ 1 / 3 + x)]
  have hp : (x ^ 2) ^ M ≤ (1 / 2 : ℝ) ^ M :=
    pow_le_pow_left₀ (sq_nonneg _) (by linarith) _
  have hterm : x ^ (2 * M + 1) ≤ (1 / 2 : ℝ) ^ M * (1 / 3) := by
    rw [pow_succ, pow_mul]
    exact mul_le_mul hp hx₁ hx₀ (by positivity)
  have hden : 2 * (x ^ (2 * M + 1) / (1 - x ^ 2)) ≤ (1 / 2 : ℝ) ^ M := by
    rw [← mul_div_assoc, div_le_iff₀ (by linarith : 0 < 1 - x ^ 2)]
    nlinarith [mul_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ) ^ M) (by linarith : 0 ≤ 1 / 3 - x ^ 2)]
  unfold logTruncation
  change |Real.log z - 2 * ∑ i ∈ Finset.range M, x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)| ≤ _
  have heq (a s : ℝ) : a - 2 * s = 2 * (1 / 2 * a - s) := by ring
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem two_thirds_le_logTruncation_two {M : ℕ} (hM : 1 ≤ M) :
    2 / 3 ≤ logTruncation (2 : ℝ) M := by
  have H : (∑ i ∈ Finset.range 1, (((2 : ℝ) - 1) / (2 + 1)) ^ (2 * i + 1) /
      (2 * (i : ℝ) + 1)) ≤ ∑ i ∈ Finset.range M,
      (((2 : ℝ) - 1) / (2 + 1)) ^ (2 * i + 1) / (2 * (i : ℝ) + 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hM) (fun i _ _ => by positivity)
  norm_num at H
  unfold logTruncation
  norm_num
  linarith

/-- Dividing the two finite sums gives a base-two approximation;
the denominator stays bounded away from zero for any positive term count. -/
theorem abs_logb_sub_truncation_ratio {z : ℝ} (hz : 1 ≤ z) (hz' : z ≤ 2)
    {M : ℕ} (hM : 1 ≤ M) :
    |logTruncation z M / logTruncation 2 M - Real.logb 2 z| ≤ 3 * (1 / 2 : ℝ) ^ M := by
  let a := logTruncation z M
  let b := logTruncation (2 : ℝ) M
  let t := Real.logb 2 z
  let e := (1 / 2 : ℝ) ^ M
  have hb : 2 / 3 ≤ b := two_thirds_le_logTruncation_two hM
  have hb₀ : 0 < b := by linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht₀ : 0 ≤ t := div_nonneg (Real.log_nonneg hz) hlog.le
  have ht₁ : t ≤ 1 := (div_le_one hlog).2 (Real.log_le_log (by linarith) hz')
  have ht : t * Real.log 2 = Real.log z := div_mul_cancel₀ _ hlog.ne'
  have ha : |a - Real.log z| ≤ e := by
    rw [abs_sub_comm]; exact abs_log_sub_logTruncation hz hz' M
  have hb' : |Real.log 2 - b| ≤ e := abs_log_sub_logTruncation (by norm_num) le_rfl M
  have he : 0 ≤ e := by positivity
  have hn : |a - t * b| ≤ 2 * e := calc
    |a - t * b| = |(a - Real.log z) + t * (Real.log 2 - b)| := by
      congr 1; nlinarith only [ht]
    _ ≤ |a - Real.log z| + |t * (Real.log 2 - b)| := abs_add_le _ _
    _ = |a - Real.log z| + t * |Real.log 2 - b| := by rw [abs_mul, abs_of_nonneg ht₀]
    _ ≤ e + 1 * e := add_le_add ha (mul_le_mul ht₁ hb' (abs_nonneg _) (by norm_num))
    _ = 2 * e := by ring
  change |a / b - t| ≤ 3 * e
  rw [show a / b - t = (a - t * b) / b by field_simp,
    abs_div, abs_of_pos hb₀, div_le_iff₀ hb₀]
  nlinarith [mul_nonneg he (sub_nonneg.mpr hb)]

/-- At the manuscript's precision parameter `η = 2⁻ᵏ`, the rational ratio using
`k+6` terms has absolute error strictly below `η/4`. -/
theorem abs_rational_logbTruncation {z : ℚ} (hz : 1 ≤ z) (hz' : z ≤ 2) (k : ℕ) :
    |((logTruncation z (k + 6) / logTruncation (2 : ℚ) (k + 6) : ℚ) : ℝ) -
      Real.logb 2 (z : ℝ)| < (1 / 2 : ℝ) ^ k / 4 := by
  push_cast
  rw [cast_logTruncation, cast_logTruncation]
  norm_num only [Rat.cast_ofNat]
  have H := abs_logb_sub_truncation_ratio (z := (z : ℝ)) (by exact_mod_cast hz)
    (by exact_mod_cast hz') (M := k + 6) (by omega)
  rw [pow_add] at H
  norm_num at H
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]

/-- Binary search reads one predicate reply per level. The returned numerator
uses denominator `2^k`; the list records the replies in reverse order. -/
def dyadicSearch (test : ℕ → ℕ → Bool) : ℕ → ℕ × List Bool
  | 0 => (0, [])
  | k + 1 =>
    let prev := dyadicSearch test k
    let bit := test (2 * prev.1 + 1) (k + 1)
    (2 * prev.1 + bit.toNat, bit :: prev.2)

theorem dyadicSearch_replies (test : ℕ → ℕ → Bool) (k : ℕ) :
    ((dyadicSearch test k).2).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [dyadicSearch, ih]

theorem dyadicSearch_numerator_lt (test : ℕ → ℕ → Bool) (k : ℕ) :
    (dyadicSearch test k).1 < 2 ^ k := by
  induction k with
  | zero => simp [dyadicSearch]
  | succ k ih =>
    simp only [dyadicSearch, pow_succ]
    cases test (2 * (dyadicSearch test k).1 + 1) (k + 1) <;> simp_all <;> omega

/-- Every query to the rational between-zero-and-one test is an integer
comparison after multiplication by a positive power of two. -/
def dyadicTest {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (s : K) (p k : ℕ) : Bool := decide ((p : K) ≤ 2 ^ k * s)

theorem dyadicSearch_brackets {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {s : K} (hs : 0 ≤ s) (hs' : s ≤ 1) (k : ℕ) :
    ((dyadicSearch (dyadicTest s) k).1 : K) ≤ 2 ^ k * s ∧
      2 ^ k * s ≤ ((dyadicSearch (dyadicTest s) k).1 : K) + 1 := by
  induction k with
  | zero => simpa [dyadicSearch] using And.intro hs hs'
  | succ k ih =>
    let p := (dyadicSearch (dyadicTest s) k).1
    change (p : K) ≤ 2 ^ k * s ∧ 2 ^ k * s ≤ (p : K) + 1 at ih
    rw [dyadicSearch]
    change (((2 * p + (dyadicTest s (2 * p + 1) (k + 1)).toNat : ℕ) : K) ≤ 2 ^ (k+1) * s) ∧
      2 ^ (k+1) * s ≤ ((2 * p + (dyadicTest s (2 * p + 1) (k+1)).toNat : ℕ) : K) + 1
    by_cases hm : ((2 * p + 1 : ℕ) : K) ≤ 2 ^ (k + 1) * s
    · have hb : dyadicTest s (2 * p + 1) (k + 1) = true := decide_eq_true hm
      simp only [hb, Bool.toNat_true, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        pow_succ] at hm ⊢
      constructor <;> nlinarith [ih.1, ih.2]
    · have hb : dyadicTest s (2 * p + 1) (k + 1) = false := decide_eq_false hm
      simp only [hb, Bool.toNat_false, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        pow_succ, Nat.cast_zero] at hm ⊢
      constructor <;> nlinarith [ih.1, ih.2]

private theorem truncationRatio_bounds {z : ℚ} (hz : 1 ≤ z) (hz' : z ≤ 2)
    {M : ℕ} (hM : 1 ≤ M) :
    0 ≤ logTruncation z M / logTruncation (2 : ℚ) M ∧
      logTruncation z M / logTruncation (2 : ℚ) M ≤ 1 := by
  have hcast := cast_logTruncation (2 : ℚ) M
  norm_num only [Rat.cast_ofNat] at hcast
  have hpos := two_thirds_le_logTruncation_two hM
  rw [← hcast] at hpos
  have hn : 0 < logTruncation (2 : ℚ) M := by
    exact_mod_cast (show 0 < ((logTruncation (2 : ℚ) M : ℚ) : ℝ) by linarith)
  have hx₀ : 0 ≤ (z - 1) / (z + 1) := div_nonneg (by linarith) (by linarith)
  have hx₁ : (z - 1) / (z + 1) ≤ ((2 : ℚ) - 1) / (2 + 1) := by
    apply (div_le_iff₀ (by linarith : 0 < z + 1)).2
    linarith
  constructor
  · apply div_nonneg _ hn.le
    unfold logTruncation
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ =>
      div_nonneg (pow_nonneg hx₀ _) (by positivity)))
  · apply (div_le_one hn).2
    unfold logTruncation
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro i _
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hx₀ hx₁ _) (by positivity)

/-- The finite grid search for the reduced factor. Its output is an explicit
integer numerator with denominator `2^(k+2)`. -/
def mantissaGridNumerator {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (z : K) (k : ℕ) : ℕ × List Bool :=
  let s := logTruncation z (k + 6) / logTruncation (2 : K) (k + 6)
  dyadicSearch (dyadicTest s) (k + 2)

theorem mantissaGrid_cost {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (z : K) (k : ℕ) :
    (mantissaGridNumerator z k).2.length = k + 2 ∧
      (mantissaGridNumerator z k).1 < 2 ^ (k + 2) :=
  ⟨dyadicSearch_replies _ _, dyadicSearch_numerator_lt _ _⟩

/-- After grid quantization the dyadic mantissa is within `η/2` of the true
base-two logarithm, with `η = (1/2)^k`. -/
theorem mantissaGrid_error {z : ℚ} (hz : 1 ≤ z) (hz' : z ≤ 2) (k : ℕ) :
    |((mantissaGridNumerator z k).1 : ℝ) / 2 ^ (k + 2) - Real.logb 2 (z : ℝ)| <
      (1 / 2 : ℝ) ^ k / 2 := by
  let s := logTruncation z (k + 6) / logTruncation (2 : ℚ) (k + 6)
  let p := (mantissaGridNumerator z k).1
  let d := (2 : ℝ) ^ (k + 2)
  have hd : 0 < d := by positivity
  obtain ⟨hs₀, hs₁⟩ := truncationRatio_bounds hz hz' (M := k + 6) (by omega)
  obtain ⟨hl, hu⟩ := dyadicSearch_brackets hs₀ hs₁ (k + 2)
  change (p : ℚ) ≤ 2 ^ (k + 2) * s at hl
  change 2 ^ (k + 2) * s ≤ (p : ℚ) + 1 at hu
  have hl' : (p : ℝ) ≤ d * (s : ℝ) := by dsimp only [d]; exact_mod_cast hl
  have hu' : d * (s : ℝ) ≤ (p : ℝ) + 1 := by dsimp only [d]; exact_mod_cast hu
  have hb : |(p : ℝ) / d - (s : ℝ)| ≤ 1 / d := by
    have lo := (div_le_iff₀ hd).2 (mul_comm d (s : ℝ) ▸ hl')
    rw [abs_of_nonpos (sub_nonpos.mpr lo), show -((p : ℝ) / d - (s : ℝ)) =
      (d * (s : ℝ) - (p : ℝ)) / d by field_simp; ring, div_le_div_iff_of_pos_right hd]
    linarith
  have HE := abs_rational_logbTruncation hz hz' k
  have he : 1 / d = (1 / 2 : ℝ) ^ k / 4 := by
    dsimp [d]; rw [pow_add, one_div_pow]; ring
  change |(p : ℝ) / d - Real.logb 2 (z : ℝ)| < _
  calc
    _ ≤ |(p : ℝ) / d - (s : ℝ)| + |(s : ℝ) - Real.logb 2 (z : ℝ)| :=
      abs_sub_le _ _ _
    _ < 1 / d + (1 / 2 : ℝ) ^ k / 4 := add_lt_add_of_le_of_lt hb HE
    _ = _ := by rw [he]; ring

theorem sum_den_dvd {ι : Type*} (s : Finset ι) (f : ι → ℚ) (D : ℕ)
    (h : ∀ i ∈ s, (f i).den ∣ D) : (∑ i ∈ s, f i).den ∣ D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    rw [Finset.sum_insert his]
    exact (Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd
      (h i (Finset.mem_insert_self i s)) (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))))

private theorem oddTerm_den_dvd (x : ℚ) (j : ℕ) (hj : 0 < j) :
    (x ^ j / (j : ℚ)).den ∣ x.den ^ j * j := by
  rw [div_eq_mul_inv]
  have hden : ((j : ℚ)⁻¹).den = j := by simp [Rat.den_inv, hj.ne']
  simpa only [Rat.den_pow, hden] using Rat.mul_den_dvd (x ^ j) (j : ℚ)⁻¹

/-- A single common denominator works simultaneously for every partial sum
encountered up to the prescribed number of terms. -/
theorem logTruncation_den_dvd {m M : ℕ} (hm : m ≤ M) (z : ℚ) :
    (logTruncation z m).den ∣
      ((z - 1) / (z + 1)).den ^ (2 * M) * (2 * M).factorial := by
  let x := (z - 1) / (z + 1)
  let d := x.den ^ (2 * M) * (2 * M).factorial
  let f (i : ℕ) := x ^ (2 * i + 1) / (2 * (i : ℚ) + 1)
  have H : (∑ i ∈ Finset.range m, f i).den ∣ d := by
    apply sum_den_dvd
    intro i hi
    have hle : 2 * i + 1 ≤ 2 * M := by have := Finset.mem_range.mp hi; omega
    have hterm := oddTerm_den_dvd x (2 * i + 1) (by omega)
    push_cast at hterm
    exact hterm.trans (Nat.mul_dvd_mul (pow_dvd_pow _ hle) (Nat.dvd_factorial (by omega) hle))
  apply Dvd.dvd.trans (Rat.mul_den_dvd (2 : ℚ) (∑ i ∈ Finset.range m, f i))
  simpa only [show (2 : ℚ).den = 1 by decide, one_mul] using H

private theorem logTruncation_nonneg_le {z : ℚ} (hz : 1 ≤ z) (M : ℕ) :
    0 ≤ logTruncation z M ∧ logTruncation z M ≤ 2 * (M : ℚ) := by
  let x := (z - 1) / (z + 1)
  have hpos : 0 < z + 1 := by linarith
  have hx₀ : 0 ≤ x := div_nonneg (by linarith) hpos.le
  have hx₁ : x ≤ 1 := (div_le_one hpos).2 (by linarith)
  have hs : ∑ i ∈ Finset.range M, x ^ (2 * i + 1) / (2 * (i : ℚ) + 1) ≤ (M : ℚ) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range M, (1 : ℚ) := by
        apply Finset.sum_le_sum
        intro i _
        apply (div_le_one (by positivity)).2
        have hp : x ^ (2 * i + 1) ≤ 1 := pow_le_one₀ hx₀ hx₁
        linarith [show (0 : ℚ) ≤ i by positivity]
      _ = _ := by simp
  constructor
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ =>
      div_nonneg (pow_nonneg hx₀ _) (by positivity)))
  · exact mul_le_mul_of_nonneg_left hs (by norm_num)

theorem numerator_le_mul_den {q : ℚ} {n : ℕ} (hq₀ : 0 ≤ q) (hq : q ≤ n) :
    q.num.natAbs ≤ n * q.den := by
  have hpos : 0 < (q.den : ℚ) := by exact_mod_cast q.den_pos
  have hr : (q.num : ℚ) / (q.den : ℚ) = q := q.num_div_den
  have H : (q.num : ℚ) ≤ (n : ℚ) * (q.den : ℚ) := (div_le_iff₀ hpos).1 (by rw [hr]; exact hq)
  have hi : q.num ≤ ((n * q.den : ℕ) : ℤ) := by exact_mod_cast H
  have hcast : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq₀)
  exact_mod_cast hcast ▸ hi

/-- Reduced numerators and denominators of every partial sum have binary
size polynomial in the truncation order and the binary size of the reduced
argument's denominator. -/
theorem logTruncation_bitSize {z : ℚ} (hz : 1 ≤ z) {m M : ℕ} (hm : m ≤ M) :
    let w := (z - 1) / (z + 1)
    let B := 2 * M * (2 * M + w.den.size) + 2 * M + 1
    (logTruncation z m).den.size ≤ B ∧ (logTruncation z m).num.natAbs.size ≤ B := by
  let w := (z - 1) / (z + 1)
  let s := 2 * M
  let D := w.den ^ s * s.factorial
  let e := s * (s + w.den.size)
  have hdpos : 0 < D := Nat.mul_pos (pow_pos w.den_pos _) (Nat.factorial_pos _)
  have hden : (logTruncation z m).den ≤ D :=
    Nat.le_of_dvd hdpos (logTruncation_den_dvd hm z)
  have hpow : D ≤ 2 ^ e := by
    calc
      D ≤ (2 ^ w.den.size) ^ s * (2 ^ s) ^ s :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.lt_size_self _).le _)
          ((Nat.factorial_le_pow s).trans (Nat.pow_le_pow_left (show s < 2 ^ s from Nat.lt_two_pow_self).le _))
      _ = _ := by simp [e, ← pow_mul, ← pow_add]; ring
  obtain ⟨hlo, hup⟩ := logTruncation_nonneg_le hz m
  have hup' : logTruncation z m ≤ (s : ℚ) := by
    dsimp [s]; push_cast; exact hup.trans (by exact_mod_cast Nat.mul_le_mul_left 2 hm)
  have hnum : (logTruncation z m).num.natAbs ≤ s * D :=
    (numerator_le_mul_den hlo hup').trans (Nat.mul_le_mul_left _ hden)
  have hmax : s * D ≤ 2 ^ (e + s) := by
    rw [pow_add, Nat.mul_comm]; exact Nat.mul_le_mul hpow (show s < 2 ^ s from Nat.lt_two_pow_self).le
  change (logTruncation z m).den.size ≤ e + s + 1 ∧
    (logTruncation z m).num.natAbs.size ≤ e + s + 1
  constructor
  · exact (Nat.size_le_size (hden.trans hpow)).trans (by rw [Nat.size_pow]; omega)
  · simpa only [Nat.size_pow] using Nat.size_le_size (hnum.trans hmax)

/-- On the mantissa interval its transformed argument has denominator at most
three times the square of the input denominator. -/
theorem mantissaArgument_den_le {z : ℚ} (hz : 1 ≤ z) (hz' : z ≤ 2) :
    ((z - 1) / (z + 1)).den ≤ 3 * z.den ^ 2 := by
  have hpos : 0 < z + 1 := by linarith
  have hnum := numerator_le_mul_den (q := z + 1) (n := 3) hpos.le (by norm_num; linarith)
  have he : (z + 1).den = z.den := by simp
  rw [he] at hnum
  have hden : (z - 1).den = z.den := by simp
  have hn : 0 < (z + 1).num.natAbs := Int.natAbs_pos.mpr (by simpa using hpos.ne')
  have hd := Rat.mul_den_dvd (z - 1) ((z + 1)⁻¹)
  rw [Rat.den_inv_of_ne_zero hpos.ne', hden] at hd
  rw [div_eq_mul_inv]
  exact (Nat.le_of_dvd (Nat.mul_pos z.den_pos hn) hd).trans
    ((Nat.mul_le_mul_left z.den hnum).trans_eq (by ring))

end Compression
end LinearProgramming
end Optimization
end OAI

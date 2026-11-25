import OAI.Optimization.LinearProgramming.Compression.ProxySeries
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Rational Taylor approximation and dyadic output for normalized minor magnitudes. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Finset
open scoped BigOperators

/-- The finite Taylor sum, evaluated in the rationals by the oracle. -/
def expTruncation {K : Type*} [Field K] (x : K) (n : ℕ) : K :=
  ∑ i ∈ range n, x ^ i / i.factorial

private theorem cast_expTruncation (x : ℚ) (n : ℕ) :
    ((expTruncation x n : ℚ) : ℝ) = expTruncation (x : ℝ) n := by
  simp [expTruncation]

private theorem expTruncation_error {x : ℝ} (hx : |x| ≤ 1) (k : ℕ) :
    |expTruncation x (k + 6) - Real.exp x| ≤ 4 * (1 / 2 : ℝ) ^ (k + 6) := by
  let n := k + 6
  have hn : 0 < n := by dsimp [n]; omega
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnz : (0 : ℝ) < n := by positivity
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos _
  have hl : (2 : ℝ) ^ (k + 5) ≤ n.factorial := by
    have h := @Nat.factorial_mul_pow_le_factorial 1 (k + 5)
    norm_num at h
    change (2 : ℝ) ^ (k + 5) ≤ ((k + 6).factorial : ℝ)
    exact_mod_cast (show 2 ^ (k + 5) ≤ (k + 6).factorial by
      simpa [show 1 + (k + 5) = k + 6 by omega] using h)
  have hrat : ((n.succ : ℕ) : ℝ) / (n.factorial * n) ≤ 2 / n.factorial := by
    rw [div_le_div_iff₀ (mul_pos hf hnz) hf, Nat.cast_succ]
    nlinarith [mul_nonneg hf.le (sub_nonneg.mpr hnr)]
  have hp : |x| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  rw [abs_sub_comm, expTruncation]
  calc
    _ ≤ |x| ^ n * (n.succ / (n.factorial * n)) := Real.exp_bound hx hn
    _ ≤ 1 * (n.succ / (n.factorial * n) : ℝ) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ ≤ 2 / (2 : ℝ) ^ (k + 5) := by
      rw [one_mul]
      exact hrat.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) hl)
    _ = 4 * (1 / 2 : ℝ) ^ (k + 6) := by rw [pow_succ, one_div_pow]; ring

/-- The approximation to `2^z` on the fractional interval uses exactly `B+6`
terms in each of the logarithm and exponential series. -/
def fractionalPowerApprox (z : ℚ) (B : ℕ) : ℚ :=
  expTruncation (z * Compression.logTruncation (2 : ℚ) (B + 6)) (B + 6)

theorem fractionalPowerApprox_error {z : ℚ} (hz : 0 ≤ z) (hz' : z ≤ 1) (B : ℕ) :
    |((fractionalPowerApprox z B : ℚ) : ℝ) - (2 : ℝ) ^ (z : ℝ)| ≤
      8 * (1 / 2 : ℝ) ^ (B + 6) := by
  let L := Compression.logTruncation (2 : ℝ) (B + 6)
  let e := (1 / 2 : ℝ) ^ (B + 6)
  have hzR : (0 : ℝ) ≤ z := by exact_mod_cast hz
  have hzR' : (z : ℝ) ≤ 1 := by exact_mod_cast hz'
  have hEL : |Real.log 2 - L| ≤ e :=
    Compression.abs_log_sub_logTruncation (by norm_num) le_rfl _
  have he : e ≤ 1 / 64 := by
    dsimp only [e]
    rw [pow_add]
    norm_num
    linarith [pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := B)]
  have hL₀ : 0 ≤ L := by
    have h := Compression.two_thirds_le_logTruncation_two (M := B + 6) (by omega)
    dsimp only [L]
    linarith
  have hL₁ : L ≤ 1 := by
    have h := (abs_le.mp hEL).1
    linarith [Real.log_two_lt_d9]
  let x := (z : ℝ) * L
  let y := Real.log 2 * (z : ℝ)
  have hx : |x| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg hzR hL₀)]
    exact (mul_le_mul hzR' hL₁ hL₀ zero_le_one).trans_eq (one_mul _)
  have hxy : |x - y| ≤ e := by
    have h : x - y = (z : ℝ) * (L - Real.log 2) := by dsimp [x,y]; ring
    rw [h, abs_mul, abs_of_nonneg hzR, abs_sub_comm L]
    exact (mul_le_mul_of_nonneg_right hzR' (abs_nonneg _)).trans ((one_mul _).le.trans hEL)
  have hy : Real.exp y = (2 : ℝ) ^ (z : ℝ) :=
    (Real.rpow_def_of_pos (by norm_num) _).symm
  have hy' : Real.exp y ≤ 2 := by
    rw [hy]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hzR'
  have habs : |Real.exp x - Real.exp y| ≤ 4 * e := by
    have h := Real.abs_exp_sub_one_le (hxy.trans (by linarith : e ≤ 1))
    rw [show Real.exp x - Real.exp y = Real.exp y * (Real.exp (x-y) - 1) by
      rw [mul_sub, ← Real.exp_add, add_sub_cancel, mul_one], abs_mul,
      abs_of_pos (Real.exp_pos y)]
    calc
      _ ≤ 2 * (2 * |x-y|) := mul_le_mul hy' h (abs_nonneg _) (by norm_num)
      _ ≤ 4 * e := by linarith
  have hTaylor := expTruncation_error hx B
  change |((expTruncation (z * Compression.logTruncation 2 (B + 6)) (B+6) : ℚ) : ℝ) -
    (2 : ℝ) ^ (z : ℝ)| ≤ _
  rw [cast_expTruncation, Rat.cast_mul, Compression.cast_logTruncation, Rat.cast_ofNat, ← hy]
  change |expTruncation x (B + 6) - Real.exp y| ≤ 8 * e
  exact (abs_sub_le _ (Real.exp x) _).trans (by linarith)


/-- Decompose the explicit rational exponent into its integer and fractional
parts. This branch is evaluated only when the integer part lies in `[-B,0]`. -/
def reducedPowerApprox (θ : ℚ) (B : ℕ) : ℚ :=
  (2 : ℚ) ^ ⌊θ⌋ * fractionalPowerApprox (Int.fract θ) B

private lemma reducedPowerApprox_error {θ : ℚ} (hθ : θ ≤ 0) (B : ℕ) :
    |((reducedPowerApprox θ B : ℚ) : ℝ) - (2 : ℝ) ^ (θ : ℝ)| ≤
      8 * (1 / 2 : ℝ) ^ (B + 6) := by
  have h := fractionalPowerApprox_error (Int.fract_nonneg θ) (Int.fract_lt_one θ).le B
  have hsplit : (θ : ℝ) = (⌊θ⌋ : ℝ) + ((Int.fract θ : ℚ) : ℝ) := by
    exact_mod_cast (Int.floor_add_fract θ).symm
  have hpow : 0 ≤ (2 : ℝ) ^ ⌊θ⌋ := by positivity
  have hpow' : (2 : ℝ) ^ ⌊θ⌋ ≤ 1 := by
    rw [← Real.rpow_intCast]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    exact_mod_cast Int.floor_nonpos hθ
  rw [reducedPowerApprox, Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat,
    hsplit, Real.rpow_add (by norm_num : 0 < (2 : ℝ)), Real.rpow_intCast,
    ← mul_sub, abs_mul, abs_of_nonneg hpow]
  exact (mul_le_mul_of_nonneg_right hpow' (abs_nonneg _)).trans ((one_mul _).le.trans h)

private def capUnit (x : ℚ) : ℚ := max 0 (min x 1)

private lemma capUnit_error (x : ℚ) {y : ℝ} (hy : 0 ≤ y) (hy' : y ≤ 1) :
    |((capUnit x : ℚ) : ℝ) - y| ≤ |(x : ℝ) - y| := by
  rcases le_or_gt x 0 with hx | hx
  · have hx' : (x : ℝ) ≤ 0 := by exact_mod_cast hx
    simp only [capUnit, min_eq_left (hx.trans zero_le_one), max_eq_left hx, Rat.cast_zero,
      zero_sub, abs_neg, abs_of_nonneg hy, abs_of_nonpos (sub_nonpos.mpr (hx'.trans hy))]
    linarith
  · rcases le_or_gt x 1 with h | h
    · simp [capUnit, min_eq_left h, max_eq_right hx.le]
    · have h' : (1 : ℝ) < x := by exact_mod_cast h
      simp only [capUnit, min_eq_right h.le, max_eq_right zero_le_one, Rat.cast_one,
        abs_of_nonneg (sub_nonneg.mpr hy'), abs_of_nonneg (sub_nonneg.mpr (hy'.trans h'.le))]
      linarith

/-- Dyadic numerator of a rounded magnitude. The pivot (`θ=0`) is exact.
Values below `-B` are dropped before any large negative power is formed. -/
def roundedPowerNumerator (θ : ℚ) (B : ℕ) : ℕ :=
  if θ = 0 then 2 ^ (B + 1)
  else if θ < -(B : ℚ) then 0
  else ⌊(2 ^ (B + 1) : ℚ) * capUnit (reducedPowerApprox θ B)⌋₊

/-- All returned entries share the denominator `2^(B+1)`. -/
def roundedPower (θ : ℚ) (B : ℕ) : ℚ :=
  (roundedPowerNumerator θ B : ℚ) / 2 ^ (B + 1)

theorem roundedPowerNumerator_le (θ : ℚ) (B : ℕ) :
    roundedPowerNumerator θ B ≤ 2 ^ (B + 1) := by
  unfold roundedPowerNumerator
  split_ifs with h₀ hsmall
  · rfl
  · exact Nat.zero_le _
  · apply Nat.floor_le_of_le
    push_cast
    have h : capUnit (reducedPowerApprox θ B) ≤ 1 :=
      max_le zero_le_one (min_le_right _ _)
    exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (mul_one _)

@[simp] theorem roundedPower_zero (B : ℕ) : roundedPower 0 B = 1 := by
  simp [roundedPower, roundedPowerNumerator]

theorem roundedPower_bounds (θ : ℚ) (B : ℕ) : 0 ≤ roundedPower θ B ∧ roundedPower θ B ≤ 1 := by
  refine ⟨by unfold roundedPower; positivity, (div_le_one (by positivity)).2 ?_⟩
  exact_mod_cast roundedPowerNumerator_le θ B

theorem roundedPower_error {θ : ℚ} (hθ : θ ≤ 0) (B : ℕ) :
    |((roundedPower θ B : ℚ) : ℝ) - (2 : ℝ) ^ (θ : ℝ)| ≤ (1 / 2 : ℝ) ^ B := by
  by_cases hz : θ = 0
  · subst θ
    simp only [roundedPower_zero, Rat.cast_one, Rat.cast_zero, Real.rpow_zero, sub_self, abs_zero]
    positivity
  have hθR : (θ : ℝ) ≤ 0 := by exact_mod_cast hθ
  have hy : 0 ≤ (2 : ℝ) ^ (θ : ℝ) := Real.rpow_nonneg (by norm_num) _
  by_cases hsmall : θ < -(B : ℚ)
  · rw [roundedPower, roundedPowerNumerator, ite_eq_right hz, ite_eq_left hsmall]
    simp only [Nat.cast_zero, zero_div, Rat.cast_zero, zero_sub, abs_neg, abs_of_nonneg hy]
    have h' : (θ : ℝ) ≤ -(B : ℝ) := by exact_mod_cast hsmall.le
    calc
      _ ≤ (2 : ℝ) ^ (-(B : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h'
      _ = (1 / 2 : ℝ) ^ B := by rw [Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ)),
          Real.rpow_natCast, one_div_pow, one_div]
  · let x := capUnit (reducedPowerApprox θ B)
    let D : ℚ := 2 ^ (B + 1)
    have hx : 0 ≤ x := le_max_left _ _
    have hD : 0 < D := by dsimp [D]; positivity
    have hN : roundedPowerNumerator θ B = ⌊D * x⌋₊ := by
      simp [roundedPowerNumerator, hz, hsmall, D, x]
    have hgrid : |roundedPower θ B - x| ≤ 1 / D := by
      rw [roundedPower, hN]
      change |(⌊D*x⌋₊ : ℚ) / D - x| ≤ 1 / D
      have hlo := Nat.floor_le (mul_nonneg hD.le hx)
      have hhi := Nat.lt_floor_add_one (D*x)
      rw [abs_of_nonpos (sub_nonpos.mpr
        ((div_le_iff₀ hD).2 (hlo.trans_eq (mul_comm _ _)))), neg_sub]
      apply (le_div_iff₀ hD).2
      rw [sub_mul, div_mul_cancel₀ _ hD.ne']
      linarith [mul_comm D x]
    have hgridR : |((roundedPower θ B : ℚ) : ℝ) - (x : ℝ)| ≤ (1 / 2 : ℝ) ^ (B + 1) := by
      rw [one_div_pow]
      dsimp only [D] at hgrid
      have hh := Rat.cast_le (K := ℝ) |>.mpr hgrid
      push_cast at hh
      exact hh
    have happ := (capUnit_error (reducedPowerApprox θ B) hy
      (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hθR)).trans
      (reducedPowerApprox_error hθ B)
    change |(x : ℝ) - 2 ^ (θ : ℝ)| ≤ _ at happ
    refine (abs_sub_le _ (x : ℝ) _).trans ((add_le_add hgridR happ).trans ?_)
    rw [pow_succ, pow_add]
    norm_num
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) B]

/-- When the Taylor branch is used, evaluation of the integer factor never
requires an exponent with magnitude greater than the precision parameter. -/
theorem reducedPowerApprox_exponent_bound {θ : ℚ} {B : ℕ}
    (hl : -(B : ℚ) ≤ θ) (hu : θ ≤ 0) : -(B : ℤ) ≤ ⌊θ⌋ ∧ ⌊θ⌋ ≤ 0 := by
  refine ⟨Int.le_floor.mpr ?_, Int.floor_nonpos hu⟩
  simpa using hl


/-- One polynomial-bit denominator serves all prefixes of the exponential sum. -/
theorem expTruncation_den_dvd (x : ℚ) {m M : ℕ} (hm : m ≤ M) :
    (expTruncation x m).den ∣ x.den ^ M * M.factorial := by
  apply Compression.sum_den_dvd
  intro i hi
  have hiM : i ≤ M := (Finset.mem_range.mp hi).le.trans hm
  have hiPos := Nat.factorial_pos i
  have hiDen : (((i.factorial : ℕ) : ℚ)⁻¹).den = i.factorial := by
    simp [Rat.den_inv, hiPos.ne']
  rw [div_eq_mul_inv]
  have h := Rat.mul_den_dvd (x ^ i) ((i.factorial : ℚ)⁻¹)
  rw [Rat.den_pow, hiDen] at h
  exact h.trans (Nat.mul_dvd_mul (pow_dvd_pow _ hiM) (Nat.factorial_dvd_factorial hiM))

/-- Polynomial-size numerator and denominator of every partial exponential
sum on the reduced interval. The bound depends on the input denominator
through its binary length. -/
theorem expTruncation_bitSize {x : ℚ} (hx : 0 ≤ x) (hx' : x ≤ 1) {m M : ℕ} (hm : m ≤ M) :
    let L := M * (x.den.size + M) + M + 1
    (expTruncation x m).den.size ≤ L ∧ (expTruncation x m).num.natAbs.size ≤ L := by
  let D := x.den ^ M * M.factorial
  let E := M * (x.den.size + M)
  have hd : 0 < D := Nat.mul_pos (pow_pos x.den_pos _) (Nat.factorial_pos _)
  have hden := Nat.le_of_dvd hd (expTruncation_den_dvd x hm)
  have hpow : D ≤ 2 ^ E := by
    calc
      D ≤ (2 ^ x.den.size) ^ M * (2 ^ M) ^ M :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.lt_size_self _).le _)
          ((Nat.factorial_le_pow M).trans (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _))
      _ = _ := by simp [E, ← pow_mul, ← pow_add]; ring
  have hsum : expTruncation x m ≤ (M : ℚ) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range m, (1 : ℚ) := by
        apply Finset.sum_le_sum
        intro i _
        have hf : (1 : ℚ) ≤ i.factorial := by exact_mod_cast Nat.factorial_pos _
        exact (div_le_one (by positivity)).2 ((pow_le_one₀ hx hx').trans hf)
      _ = (m : ℚ) := by simp
      _ ≤ M := by exact_mod_cast hm
  have hs₀ : 0 ≤ expTruncation x m := Finset.sum_nonneg fun i _ =>
    div_nonneg (pow_nonneg hx i) (by positivity)
  have hnum := (Compression.numerator_le_mul_den hs₀ hsum).trans (Nat.mul_le_mul_left M hden)
  have hnum' : M * D ≤ 2 ^ (E + M) := by
    rw [pow_add, Nat.mul_comm]; exact Nat.mul_le_mul hpow Nat.lt_two_pow_self.le
  change (expTruncation x m).den.size ≤ E + M + 1 ∧
    (expTruncation x m).num.natAbs.size ≤ E + M + 1
  constructor
  · exact (Nat.size_le_size (hden.trans hpow)).trans (by rw [Nat.size_pow]; omega)
  · simpa only [Nat.size_pow] using Nat.size_le_size (hnum.trans hnum')

/-- Before every partial exponential sum is evaluated, its rational argument
has denominator size polynomial in the input exponent size and precision. -/
theorem reducedTaylorArgument_den_size (θ : ℚ) (M : ℕ) :
    (Int.fract θ * Compression.logTruncation 2 M).den.size ≤
      θ.den.size + (2 * M * (2 * M + 2) + 2 * M + 1) := by
  let q := Compression.logTruncation (2 : ℚ) M
  have hsize : q.den.size ≤ 2 * M * (2 * M + 2) + 2 * M + 1 := by
    have h : (((2 : ℚ) - 1) / (2 + 1)).den.size = 2 := by
      rw [show ((2 : ℚ) - 1) / (2 + 1) = 1 / 3 by norm_num]
      have hden : (1 / 3 : ℚ).den = 3 := by
        rw [one_div, Rat.den_inv_of_ne_zero (by norm_num : (3 : ℚ) ≠ 0)]
        norm_num
      rw [hden]
      apply Nat.le_antisymm (Nat.size_le.mpr (by decide))
      by_contra! hn
      have hc := Nat.size_le.mp (show (3 : ℕ).size ≤ 1 by omega)
      norm_num at hc
    simpa only [q, h] using (Compression.logTruncation_bitSize (z := 2) (by norm_num)
      (m := M) (M := M) le_rfl).1
  have hd := Nat.le_of_dvd (Nat.mul_pos (Int.fract θ).pos q.pos)
    (Rat.mul_den_dvd (Int.fract θ) q)
  rw [Rat.den_intFract] at hd
  refine (Nat.size_le.2 (hd.trans_lt ?_)).trans (Nat.add_le_add_left hsize θ.den.size)
  rw [pow_add]
  exact (Nat.mul_le_mul_right _ (Nat.lt_size_self θ.den).le).trans_lt
    (Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self q.den) (by positivity))

/-- The explicitly emitted numerator and denominator each use at most `B+2`
bits, including the exact pivot numerator. -/
theorem roundedPower_dyadic_size (θ : ℚ) (B : ℕ) :
    (roundedPowerNumerator θ B).size ≤ B + 2 ∧ (2 ^ (B + 1)).size = B + 2 := by
  constructor
  · simpa only [Nat.size_pow] using Nat.size_le_size (roundedPowerNumerator_le θ B)
  · rw [Nat.size_pow]

end Geometry
end LinearProgramming
end Optimization
end OAI

import OAI.Computability.NearSquareRoot.PrecisionDiagonal
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Log

/-!
# Digit array sizes for fixed-point convolution

With the parameters of the integer multiplication algorithm the packed array
has bit volume between `n` and `48*n`. These estimates include the partial
last digit, all invalid box addresses, and padding to a power of two.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace DigitPacking

/-- Bits in a radix digit. The logarithmic algorithm uses this for `n ≥ 2`. -/
def width (n : ℕ) : ℕ := Nat.clog 2 n

/-- Number of radix digits, including a possibly short most significant digit. -/
def count (n : ℕ) : ℕ := n ⌈/⌉ width n

/-- Address width and number of slots of the padded array. -/
def addressBits (n : ℕ) : ℕ := Nat.clog 2 (4 * count n)

def capacity (n : ℕ) : ℕ := 2 ^ addressBits n

private theorem square_le_two_pow_succ (b : ℕ) : b ^ 2 ≤ 2 ^ (b + 1) := by
  induction b with
  | zero => decide
  | succ b ih =>
    by_cases h : b < 3
    · interval_cases b <;> decide
    · rw [pow_succ 2 (b + 1)]
      have hx : (b+1)^2 ≤ 2*b^2 := by nlinarith [Nat.mul_self_le_mul_self (show 2 ≤ b-1 by omega)]
      omega

theorem width_pos {n : ℕ} (hn : 2 ≤ n) : 0 < width n := Nat.clog_pos (by decide) hn

theorem width_le (n : ℕ) : width n ≤ n :=
  Nat.clog_le_of_le_pow (Nat.lt_pow_self (by decide : 1 < 2)).le

theorem count_mul_width {n : ℕ} (hn : 2 ≤ n) :
    n ≤ width n * count n ∧ width n * count n ≤ 2*n := by
  have hb := width_pos hn
  constructor
  · exact (ceilDiv_le_iff_le_mul hb).1 (le_refl (count n))
  · have h := Nat.div_mul_le_self (n + width n - 1) (width n)
    unfold count
    rw [Nat.ceilDiv_eq_add_pred_div, mul_comm]
    have := width_le n
    omega

theorem count_pos {n : ℕ} (hn : 2 ≤ n) : 0 < count n := by
  have h := (count_mul_width hn).1
  by_contra! hh
  simp [Nat.eq_zero_of_le_zero hh] at h
  omega

theorem count_le {n : ℕ} (hn : 2 ≤ n) : count n ≤ n := by
  apply (ceilDiv_le_iff_le_mul (width_pos hn)).2
  simpa using Nat.mul_le_mul_right n (width_pos hn)

theorem count_le_radix {n : ℕ} (hn : 2 ≤ n) : count n ≤ 2 ^ width n :=
  (count_le hn).trans (Nat.le_pow_clog (by decide) n)

/-- Rounding the address width up costs less than a factor of two in slots. -/
theorem capacity_bounds {n : ℕ} (hn : 2 ≤ n) :
    4 * count n ≤ capacity n ∧ capacity n < 8 * count n := by
  refine ⟨Nat.le_pow_clog (by decide) _, ?_⟩
  have hh := count_pos hn
  have hh' : 1 < 4 * count n := by omega
  have hl := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hh'
  have hk : 0 < addressBits n := Nat.clog_pos (by decide) hh'
  change 2^(addressBits n-1) < _ at hl
  unfold capacity
  rw [show addressBits n = addressBits n - 1 + 1 by omega, pow_succ]
  omega

theorem addressBits_le {n : ℕ} (hn : 2 ≤ n) : addressBits n ≤ width n + 2 := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  have h := (count_le hn).trans (Nat.le_pow_clog (by decide : 1 < 2) n)
  change count n ≤ 2^width n at h
  omega

theorem width_le_twice_addressBits {n : ℕ} (hn : 2 ≤ n) : width n ≤ 2 * addressBits n := by
  have hb := width_pos hn
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hn
  change 2^(width n - 1) < n at hp
  have hpow : 2^(width n + 1) < 4*n := by
    rw [show width n + 1 = (width n - 1) + 2 by omega, pow_add]
    omega
  have hsq := (square_le_two_pow_succ (width n)).trans hpow.le
  have hpack := (count_mul_width hn).1
  have hwb : width n ≤ 4 * count n := by
    apply Nat.le_of_mul_le_mul_left (a := width n)
    · nlinarith only [hsq, hpack]
    · exact hb
  have hN := (capacity_bounds hn).1
  apply Nat.clog_le_of_le_pow
  calc
    n ≤ width n * count n := hpack
    _ ≤ capacity n * capacity n := Nat.mul_le_mul (hwb.trans hN) (by omega)
    _ = _ := by rw [Nat.mul_comm 2, pow_mul, pow_two]; rfl

/-- The full record array has linear bit volume including padding. -/
theorem packed_volume {n : ℕ} (hn : 2 ≤ n) :
    n ≤ capacity n * addressBits n ∧ capacity n * addressBits n ≤ 48*n := by
  obtain ⟨hpack,hpad⟩ := count_mul_width hn
  obtain ⟨hlo,hhi⟩ := capacity_bounds hn
  have hw := width_le_twice_addressBits hn
  have hk := addressBits_le hn
  have hb := width_pos hn
  constructor
  · calc
      n ≤ width n * count n := hpack
      _ ≤ (2*addressBits n) * count n := Nat.mul_le_mul_right _ hw
      _ = 2 * count n * addressBits n := by ring
      _ ≤ capacity n * addressBits n := Nat.mul_le_mul_right _ (by omega)
  · calc
      capacity n * addressBits n ≤ (8*count n)*(3*width n) :=
        Nat.mul_le_mul hhi.le (by omega)
      _ = 24 * (width n * count n) := by ring
      _ ≤ 48*n := by omega

/-- Explicit comparison of the machine's binary address length with the
natural logarithm used in the final time bound. -/
theorem addressBits_log_bounds {n : ℕ} (hn : 2 ≤ n) :
    Real.log n / Real.log 2 ≤ 2*addressBits n ∧
    (addressBits n : ℝ) ≤ 3 + Real.log n / Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hb := width_pos hn
  have hlow := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hn
  change 2^(width n-1) < n at hlow
  have hhigh : n ≤ 2^width n := Nat.le_pow_clog (by decide) _
  have hl : Real.log ((2 : ℝ)^(width n-1)) ≤ Real.log n := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hlow.le
  have hu : Real.log (n : ℝ) ≤ Real.log ((2 : ℝ)^width n) := by
    apply Real.log_le_log hn'
    exact_mod_cast hhigh
  rw [Real.log_pow, Nat.cast_sub hb, Nat.cast_one] at hl
  rw [Real.log_pow] at hu
  constructor
  · apply (div_le_iff₀ hlog).2
    have H : (width n : ℝ) ≤ 2 * addressBits n := by exact_mod_cast width_le_twice_addressBits hn
    exact hu.trans (mul_le_mul_of_nonneg_right H hlog.le)
  · have H : (addressBits n : ℝ) ≤ width n + 2 := by exact_mod_cast addressBits_le hn
    have h : (width n : ℝ) - 1 ≤ Real.log n / Real.log 2 := (le_div_iff₀ hlog).2 hl
    linarith

theorem addressBits_tendsto_atTop : Filter.Tendsto addressBits Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro t
  refine ⟨2^(2*t+1), fun n hn => ?_⟩
  have two : 2 ≤ n := le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ 2*t+1 by omega)) hn
  have h := Nat.clog_mono_right 2 hn
  rw [Nat.clog_pow 2 _ (by decide)] at h
  change 2*t+1 ≤ width n at h
  have := width_le_twice_addressBits two
  omega

/-- Any permutation or zero-padding of unsigned radix digits is an admissible
input to the forward transform's Euclidean norm estimate. -/
theorem digit_array_norm {ι : Type*} [Fintype ι] {n : ℕ} (hn : 2 ≤ n)
    (hcard : Fintype.card ι = capacity n)
    (z : EuclideanSpace ℂ ι) (hz : ∀ i, ‖z i‖ ≤ (2 : ℝ) ^ width n) :
    ‖z‖ ≤ (2 : ℝ) ^ (4*addressBits n) := by
  have hw := width_le_twice_addressBits hn
  have hcap : (Fintype.card ι : ℝ) = (2 : ℝ)^addressBits n := by
    rw [hcard, capacity, Nat.cast_pow, Nat.cast_ofNat]
  calc
    ‖z‖ ≤ Real.sqrt (Fintype.card ι) * (2 : ℝ)^width n :=
      NearSquareRoot.euclidean_norm_le_of_coordinates _ (by positivity) hz
    _ ≤ (2 : ℝ)^addressBits n * 2^width n := by
      rw [hcap]
      gcongr
      exact Real.sqrt_le_self_iff.mpr (.inr (one_le_pow₀ (by norm_num)))
    _ = (2 : ℝ)^(addressBits n + width n) := (pow_add ..).symm
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)

end DigitPacking

end NearSquareRoot
end Computability
end OAI

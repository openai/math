import OAI.Computability.NearSquareRoot.PrecisionInvSqrtWord
import OAI.Computability.NearSquareRoot.PrecisionGrid
import OAI.Computability.NearSquareRoot.SynchronizedPair

/-! # One final dyadic normalization after an exact integer Walsh transform -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication

def flatWalshBits (k : ℕ) := 90*k+2

/-- The signed integer product before the single binary shift. -/
def flatWalshProduct (k m : ℕ) (z : Grid.Cell) : Grid.Cell :=
  (invSqrtNumerator (2^m) (flatWalshBits k) : Grid.Cell)*z

def flatWalshRecord (k m : ℕ) (z : Grid.Cell) : Record k :=
  Grid.wrapMap (componentBits k) (Grid.divA (flatWalshBits k) (flatWalshProduct k m z))

private noncomputable def rawValue (k : ℕ) (z : Grid.Cell) :=
  Grid.toC z / (2 : ℂ)^fractionBits k

private noncomputable def scale (k m : ℕ) : ℝ :=
  (invSqrtNumerator (2^m) (flatWalshBits k) : ℝ)/(2:ℝ)^flatWalshBits k

private theorem sqrt_two_pow (m : ℕ) : Real.sqrt ((2 : ℝ)^m) = (Real.sqrt 2)^m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_succ (Real.sqrt 2), Real.sqrt_mul (by positivity), ih]

private theorem scale_bounds (k m : ℕ) :
    0 ≤ scale k m ∧ scale k m ≤ SynchronizedPair.w^m ∧
      |scale k m - SynchronizedPair.w^m| ≤ 1/(2:ℝ)^flatWalshBits k := by
  have hp : 0 < (2:ℕ)^m := by positivity
  have e := (invSqrtNumerator_error hp (flatWalshBits k)).le
  have h := (invSqrtNumerator_interval hp (flatWalshBits k)).1
  push_cast at e h
  rw [sqrt_two_pow] at h e
  unfold scale SynchronizedPair.w
  rw [inv_pow]
  exact ⟨by positivity, (div_le_iff₀ (by positivity)).2 h, e⟩

private theorem raw_le {k m : ℕ} (z : Grid.Cell) (hm : m ≤ k)
    (hz : ‖(SynchronizedPair.w:ℂ)^m * rawValue k z‖ ≤ (2:ℝ)^(13*k)) :
    ‖rawValue k z‖ ≤ (2:ℝ)^(14*k) := by
  have hs : 0 < Real.sqrt 2 := by positivity
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, SynchronizedPair.w,
    abs_of_pos (inv_pos.mpr hs), inv_pow, ← div_eq_inv_mul,
    div_le_iff₀ (pow_pos hs m)] at hz
  have s : (Real.sqrt 2)^m ≤ (2:ℝ)^k :=
    (pow_le_pow_left₀ hs.le (Real.sqrt_le_self_iff.mpr (Or.inr (by norm_num))) m).trans
      (pow_le_pow_right₀ (by norm_num) hm)
  calc
    _ ≤ (2:ℝ)^(13*k) * (Real.sqrt 2)^m := hz
    _ ≤ (2:ℝ)^(13*k) * 2^k := by gcongr
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem flatWalsh_input_fits {k m : ℕ} (z : Grid.Cell) (hm : m ≤ k)
    (hz : ‖(SynchronizedPair.w:ℂ)^m * (Grid.toC z/(2:ℂ)^fractionBits k)‖ ≤ (2:ℝ)^(13*k)) :
    Grid.focus (84*k+2) z := by
  have h := raw_le z hm hz
  unfold rawValue at h
  rw [norm_div, norm_pow, show ‖(2:ℂ)‖=(2:ℝ) by norm_num, div_le_iff₀ (by positivity),
    ← pow_add] at h
  refine Grid.short _ (Grid.into _) (h.trans_lt ?_)
  apply pow_lt_pow_right₀ (by norm_num)
  unfold fractionBits; omega

theorem flatWalsh_product_fits {k m : ℕ} (z : Grid.Cell) (hm : m ≤ k)
    (hz : ‖(SynchronizedPair.w:ℂ)^m * (Grid.toC z/(2:ℂ)^fractionBits k)‖ ≤ (2:ℝ)^(13*k)) :
    Grid.focus (174*k+4) (flatWalshProduct k m z) := by
  have h := raw_le z hm hz
  unfold rawValue at h
  rw [norm_div, norm_pow, show ‖(2:ℂ)‖=(2:ℝ) by norm_num, div_le_iff₀ (by positivity),
    ← pow_add] at h
  have hn : (invSqrtNumerator (2^m) (flatWalshBits k) : ℝ) ≤ (2:ℝ)^flatWalshBits k := by
    exact_mod_cast invSqrtNumerator_le (2^m) (flatWalshBits k)
  apply Grid.short _ (Grid.into _)
  rw [flatWalshProduct, map_mul, map_natCast, norm_mul, Complex.norm_natCast]
  apply (mul_le_mul hn h (norm_nonneg _) (by positivity)).trans_lt
  rw [← pow_add]
  apply pow_lt_pow_right₀ (by norm_num)
  unfold flatWalshBits fractionBits; omega

private theorem scaled_product (k m : ℕ) (z : Grid.Cell) :
    (Grid.toC (flatWalshProduct k m z) / (2:ℂ)^flatWalshBits k) / (2:ℂ)^fractionBits k =
      (scale k m : ℂ) * rawValue k z := by
  unfold flatWalshProduct scale rawValue
  rw [map_mul, map_natCast]
  push_cast
  ring

theorem flatWalsh_rounded_fits {k m : ℕ} (z : Grid.Cell)
    (hz : ‖(SynchronizedPair.w:ℂ)^m * (Grid.toC z/(2:ℂ)^fractionBits k)‖ ≤ (2:ℝ)^(13*k)) :
    Grid.focus (componentBits k) (Grid.divA (flatWalshBits k) (flatWalshProduct k m z)) := by
  have hb := scale_bounds k m
  have hnorm : ‖(scale k m:ℂ)*rawValue k z‖ ≤ (2:ℝ)^(13*k) := by
    have pos : 0 ≤ SynchronizedPair.w := by unfold SynchronizedPair.w; positivity
    apply le_trans _ hz
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hb.1, abs_of_nonneg pos]
    exact mul_le_mul_of_nonneg_right hb.2.1 (norm_nonneg _)
  rw [← scaled_product, norm_div, norm_pow, show ‖(2:ℂ)‖=(2:ℝ) by norm_num,
    div_le_iff₀ (by positivity), ← pow_add] at hnorm
  let a := flatWalshProduct k m z
  have e := Grid.embedded (flatWalshBits k) a
  have h := norm_sub_le_norm_sub_add_norm_sub (Grid.toC (Grid.divA (flatWalshBits k) a))
    (Grid.toC a/(2:ℂ)^flatWalshBits k) 0
  simp only [sub_zero] at h
  apply Grid.short _ (Grid.into _)
  obtain hh := h.trans (add_le_add e hnorm)
  apply hh.trans_lt
  have gap : 13*k + fractionBits k + 2 ≤ componentBits k := by
    unfold fractionBits componentBits; omega
  apply lt_of_lt_of_le _ (pow_le_pow_right₀ (by norm_num) gap)
  rw [pow_add _ _ 2]; norm_num
  linarith [one_le_pow₀ (by norm_num : 1 ≤ (2:ℝ)) (a := 2) (n := 13*k+fractionBits k)]

/-- Both the rational coefficient error and the final signed truncation,
after multiplying an unrestricted integer Walsh result. -/
theorem flatWalshRecord_error {k m : ℕ} (z : Grid.Cell) (hk : 1≤k) (hm : m≤k)
    (hz : ‖(SynchronizedPair.w:ℂ)^m*(Grid.toC z/(2:ℂ)^fractionBits k)‖ ≤ (2:ℝ)^(13*k)) :
    ‖value k (flatWalshRecord k m z) -
      (SynchronizedPair.w:ℂ)^m*(Grid.toC z/(2:ℂ)^fractionBits k)‖ ≤ 1/(2:ℝ)^(68*k) := by
  let x := rawValue k z
  let a := flatWalshProduct k m z
  have trunc : ‖value k (flatWalshRecord k m z) - (scale k m:ℂ)*x‖ ≤
      2/(2:ℝ)^fractionBits k := by
    change ‖Grid.toC (Grid.aspect (Grid.wrapMap _ (Grid.divA _ a)))/(2:ℂ)^fractionBits k -
      (scale k m:ℂ)*rawValue k z‖ ≤ _
    rw [Grid.recovers _ (flatWalsh_rounded_fits z hz), ← scaled_product, ← sub_div, norm_div,
      norm_pow, show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
    exact div_le_div_of_nonneg_right (Grid.embedded _ _) (by positivity)
  have coeff : ‖(scale k m:ℂ)*x - (SynchronizedPair.w:ℂ)^m*x‖ ≤
      (1/(2:ℝ)^flatWalshBits k) * (2:ℝ)^(14*k) := by
    rw [← sub_mul, norm_mul, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (scale_bounds k m).2.2 (raw_le z hm hz) (norm_nonneg _) (by positivity)
  apply (norm_sub_le_norm_sub_add_norm_sub _ ((scale k m:ℂ)*x) _).trans
  apply (add_le_add trunc coeff).trans
  have hl : 70*k + 14*k ≤ flatWalshBits k := by unfold flatWalshBits; omega
  have hh : 68*k + 1 ≤ 70*k := by omega
  have t : (1/(2:ℝ)^flatWalshBits k)*(2:ℝ)^(14*k) ≤ 1/(2:ℝ)^(70*k) := by
    field_simp
    simpa only [← pow_add, add_comm (14*k)] using
      (show (2:ℝ)^(70*k + 14*k) ≤ 2^flatWalshBits k from pow_le_pow_right₀ (by norm_num) hl)
  apply (add_le_add le_rfl t).trans
  rw [fractionBits, pow_succ]
  have sh := pow_le_pow_right₀ (a := (2:ℝ)) (by norm_num) hh
  rw [pow_succ] at sh
  field_simp
  linarith

end FixedPoint

end NearSquareRoot
end Computability
end OAI

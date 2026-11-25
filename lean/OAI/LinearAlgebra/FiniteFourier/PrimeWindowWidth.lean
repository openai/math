import OAI.LinearAlgebra.FiniteFourier.PrimeWindowSize

/-! # Width of the spectral-repair window

For at least two digits the base-two logarithm and both integer roundings
are absorbed into an explicit constant in the square-root width bound.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- The manuscript's rounded radius is at most
`4 (ℓ − 1) √(m log(2m))` for every radix and tuple length at least two. -/
theorem repairWindowRadius_le_sqrt_mul_log {ℓ m : ℕ} (hℓ : 2 ≤ ℓ) (hm : 2 ≤ m) :
    (repairWindowRadius ℓ m : ℝ) ≤
      (4 * ((ℓ : ℝ) - 1)) * Real.sqrt ((m : ℝ) * Real.log (2 * (m : ℝ))) := by
  let L := Real.log (2 * (m : ℝ))
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog₂ : (1 / 2 : ℝ) ≤ Real.log 2 := by
    convert Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have hL : 1 / 2 ≤ L :=
    hlog₂.trans (Real.log_le_log (by norm_num) (by linarith))
  have hlogb : 0 ≤ L / Real.log 2 := by
    exact div_nonneg (by linarith) (by linarith)
  have hr : (repairWindowR m : ℝ) ≤ 4 * L := by
    have hceil := Nat.ceil_lt_add_one hlogb
    have he : repairWindowR m = ⌈L / Real.log 2⌉₊ := by
      rw [repairWindowR, ← Real.natCeil_logb_natCast]
      simp [Real.logb, L]
    rw [he]
    have hd : L / Real.log 2 ≤ 2 * L := by
      apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).2
      nlinarith [mul_nonneg (by linarith : 0 ≤ L) (by linarith : 0 ≤ Real.log 2 - 1/2)]
    linarith
  have h₁ : 1 ≤ (m : ℝ) * L := by
    nlinarith [(mul_nonneg (by linarith : 0 ≤ (m : ℝ) - 2) (by linarith : 0 ≤ L))]
  have hroot : 1 ≤ Real.sqrt ((m : ℝ) * L) := by
    simpa using Real.sqrt_le_sqrt h₁
  have hs : Real.sqrt (2 * (m : ℝ) * repairWindowR m) ≤ 3 * Real.sqrt ((m : ℝ) * L) := by
    calc
      _ ≤ Real.sqrt (9 * ((m : ℝ) * L)) := Real.sqrt_le_sqrt (by
        nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (α := ℝ) m)])
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]; norm_num
  have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (2 * (m : ℝ) * repairWindowR m))
  rw [repairWindowRadius, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]
  change ((ℓ : ℝ) - 1) * _ ≤ (4 * ((ℓ : ℝ) - 1)) * Real.sqrt ((m : ℝ) * L)
  calc
    _ ≤ ((ℓ : ℝ) - 1) * (4 * Real.sqrt ((m : ℝ) * L)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by exact_mod_cast (by omega : 0 ≤ (ℓ : ℤ) - 1))
    _ = _ := by ring

end FiniteFourier
end LinearAlgebra
end OAI

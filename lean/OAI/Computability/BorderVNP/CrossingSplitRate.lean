import OAI.Computability.BorderVNP.CrossingRate

/-!
# Size of a balanced cut after homogeneous projection

The first homogeneous extraction in §4.3 uses at most `2 (n+1)² s` gates. Selecting
the set-multilinear coefficients gives cut width at most `ℓ(ℓq+2(n+1)²s+1)`. The
polynomial overhead is absorbed in the difference between the exponents in (4.2) and
(4.3). Reserving one input position for each of the `ℓq` one-hot bits ensures that
both `ℓ` and `q` are at most `n` when they are positive.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open Filter

/-- Explicit number of labels sufficient for one rank wire after taking degree `n`
and projecting to a form with `ℓ` parties and `q` alternatives per party. -/
def splitWidth (n ℓ q s : ℕ) : ℕ := ℓ * (ℓ * q + 2 * (n+1)^2 * s + 1)

private theorem splitWidth_le {n ℓ q s : ℕ} {B : ℝ} (hn : 4 ≤ n) (hℓ : ℓ ≤ n) (hq : q ≤ n)
    (hs : s ≤ B) (hB : 1 ≤ B) : (splitWidth n ℓ q s : ℝ) ≤ (n : ℝ)^5 * B := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hℓ' : (ℓ : ℝ) ≤ n := by exact_mod_cast hℓ
  have hq' : (q : ℝ) ≤ n := by exact_mod_cast hq
  have hsq : ((n : ℝ)+1)^2 ≤ ((n : ℝ)*2)^2 := by gcongr; linarith
  have hsmall : 1 ≤ (n : ℝ)^2 * B := one_le_mul_of_one_le_of_one_le (by nlinarith) hB
  have hwidth : (ℓ : ℝ) * q ≤ (n : ℝ)^2 * B :=
    (mul_le_mul hℓ' hq' (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans
      (by rw [← sq]; exact le_mul_of_one_le_right (sq_nonneg _) hB)
  have hcomponent : 2 * ((n : ℝ)+1)^2 * s ≤ 8 * (n : ℝ)^2 * B := by
    calc
      _ ≤ 2 * ((n : ℝ)*2)^2 * B := by gcongr
      _ = _ := by ring
  rw [splitWidth]
  push_cast
  calc
    _ ≤ (n : ℝ) * (10 * ((n : ℝ)^2 * B)) := by
      apply mul_le_mul hℓ' _ (by positivity) (Nat.cast_nonneg _)
      linarith
    _ ≤ (n : ℝ) * ((n : ℝ)^2 * ((n : ℝ)^2 * B)) := by
      gcongr
      nlinarith
    _ = _ := by ring

private theorem log_overhead {c₀ c₁ : ℝ} (h₀ : 0 < c₀) (h₁ : 0 < c₁) :
    ∀ᶠ n : ℕ in atTop, 500 * Real.logb 2 n ≤
      width c₁ n * Real.sqrt (directions c₀ (width c₁ n)) := by
  let A := Real.sqrt (c₀ / 2) * (c₁ / 2) ^ (5 / 4 : ℝ)
  have hA : 0 < A := by dsimp [A]; positivity
  have hl : Tendsto (fun n : ℕ => Real.logb 2 n) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hpow := (tendsto_rpow_atTop (show (0 : ℝ) < 1/4 by norm_num)).comp hl
  filter_upwards [width_sqrt_directions h₀ h₁, hl.eventually_gt_atTop 0,
    hpow.eventually_ge_atTop (500 / A)] with n hw hlpos hp
  let x := Real.logb 2 n
  have hfactor : 500 ≤ A * x ^ (1/4 : ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hA).mp hp
  calc
    500 * x ≤ (A * x ^ (1/4 : ℝ)) * x := mul_le_mul_of_nonneg_right hfactor hlpos.le
    _ = A * x ^ (5/4 : ℝ) := by
      rw [show (5/4 : ℝ) = 1/4 + 1 by norm_num, Real.rpow_add hlpos, Real.rpow_one, mul_assoc]
    _ ≤ _ := hw.1

/-- With `c₂ = 1/100` in (4.2), the common rank width is bounded by
`2 ^ (0.02 m √D)` for all sufficiently large lengths, simultaneously for every side. -/
theorem eventually_splitWidth_le {c₀ c₁ : ℝ} (h₀ : 0 < c₀) (h₁ : 0 < c₁) :
    ∀ᶠ n : ℕ in atTop, ∀ ℓ q s : ℕ, ℓ ≤ n → q ≤ n →
      let W := (width c₁ n : ℝ) * Real.sqrt (directions c₀ (width c₁ n))
      (s : ℝ) ≤ (2 : ℝ) ^ (W/100) → (splitWidth n ℓ q s : ℝ) ≤ (2 : ℝ) ^ (W/50) := by
  filter_upwards [log_overhead h₀ h₁, eventually_ge_atTop (4 : ℕ)] with n hlog hn
  intro ℓ q s hℓ hq W hs
  have hB : (1 : ℝ) ≤ 2 ^ (W/100) := Real.one_le_rpow (by norm_num) (by dsimp [W]; positivity)
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx : (n : ℝ)^5 = (2 : ℝ)^(5 * Real.logb 2 n) := by
    rw [mul_comm (5 : ℝ), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num) (by norm_num) hpos]
    norm_num
  calc
    _ ≤ (n : ℝ)^5 * 2 ^ (W/100) := splitWidth_le hn hℓ hq hs hB
    _ ≤ (2 : ℝ)^(W/100) * 2 ^ (W/100) := by
      rw [hx]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      dsimp [W]
      linarith only [hlog]
    _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring

end Crossing

end BorderVNP
end Computability
end OAI

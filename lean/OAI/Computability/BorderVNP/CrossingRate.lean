import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Rate of the orthogonal-wire construction

Section 4 takes `m = ⌊c₁ log₂ n⌋` bits per wire and
`D = ⌊c₀ √m⌋` directions.  These estimates include both floor errors and
compare the resulting threshold (4.2) with the conclusion of the stretch lemma.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open Filter

/-- Width of a single antipodal wire at input length `n`. -/
noncomputable def width (c₁ : ℝ) (n : ℕ) : ℕ := ⌊c₁ * Real.logb 2 n⌋₊

/-- Number of orthogonal directions at the given wire width. -/
noncomputable def directions (c₀ : ℝ) (m : ℕ) : ℕ := ⌊c₀ * Real.sqrt m⌋₊

private theorem times_sqrt_sqrt {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    x * Real.sqrt (a * Real.sqrt x) = Real.sqrt a * x ^ (5 / 4 : ℝ) := by
  rw [Real.sqrt_mul ha, Real.sqrt_eq_rpow (Real.sqrt x), Real.sqrt_eq_rpow x, ← Real.rpow_mul hx]
  rw [show (5 / 4 : ℝ) = 1 + (1 / 2) * (1 / 2) by norm_num]
  rcases eq_or_lt_of_le hx with rfl | h
  · norm_num
  · rw [Real.rpow_add h, Real.rpow_one]
    ring

private theorem nat_floor_ge_half {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one x
  linarith

/-- Both floors cost at most a factor of two eventually. The implied constants
in `m √D = Θ((log₂ n)^(5/4))` depend only on the two numerical parameters. -/
theorem width_sqrt_directions {c₀ c₁ : ℝ} (h₀ : 0 < c₀) (h₁ : 0 < c₁) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt (c₀ / 2) * (c₁ / 2) ^ (5 / 4 : ℝ) * (Real.logb 2 n) ^ (5 / 4 : ℝ) ≤
        width c₁ n * Real.sqrt (directions c₀ (width c₁ n)) ∧
      width c₁ n * Real.sqrt (directions c₀ (width c₁ n)) ≤
        Real.sqrt c₀ * c₁ ^ (5 / 4 : ℝ) * (Real.logb 2 n) ^ (5 / 4 : ℝ) := by
  have hl : Tendsto (fun n : ℕ => Real.logb 2 n) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hwidth := hl.const_mul_atTop h₁
  filter_upwards [hwidth.eventually_ge_atTop (max 2 (2 * (2 / c₀) ^ 2)),
    hl.eventually_ge_atTop 0] with n hn hx
  let x := Real.logb 2 n
  let m : ℝ := width c₁ n
  have hm : c₁ * x / 2 ≤ m := nat_floor_ge_half ((le_max_left ..).trans hn)
  have hm' : m ≤ c₁ * x := Nat.floor_le (mul_nonneg h₁.le hx)
  have hbig : (2 / c₀) ^ 2 ≤ m := by
    have h := (le_max_right ..).trans hn
    linarith
  have hD : 2 ≤ c₀ * Real.sqrt m := by
    have h := Real.sqrt_le_sqrt hbig
    rw [Real.sqrt_sq (by positivity : 0 ≤ 2 / c₀)] at h
    simpa [mul_comm] using (div_le_iff₀ h₀).mp h
  have hDlo : c₀ / 2 * Real.sqrt m ≤ (directions c₀ (width c₁ n) : ℝ) := by
    simpa [directions, m, div_mul_eq_mul_div] using nat_floor_ge_half hD
  have hDhi : (directions c₀ (width c₁ n) : ℝ) ≤ c₀ * Real.sqrt m :=
    Nat.floor_le (mul_nonneg h₀.le (Real.sqrt_nonneg _))
  have hmlo : (c₁ / 2) * x ≤ m := by linarith
  have hmnn : 0 ≤ m := Nat.cast_nonneg _
  constructor
  · calc
      _ = Real.sqrt (c₀ / 2) * ((c₁ / 2) * x) ^ (5 / 4 : ℝ) := by
        rw [Real.mul_rpow (by positivity : 0 ≤ c₁ / 2) hx]; ring
      _ ≤ Real.sqrt (c₀ / 2) * m ^ (5 / 4 : ℝ) := by gcongr
      _ = m * Real.sqrt ((c₀ / 2) * Real.sqrt m) := (times_sqrt_sqrt (by positivity) hmnn).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hDlo) hmnn
  · calc
      _ ≤ m * Real.sqrt (c₀ * Real.sqrt m) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hDhi) hmnn
      _ = Real.sqrt c₀ * m ^ (5 / 4 : ℝ) := times_sqrt_sqrt h₀.le hmnn
      _ ≤ Real.sqrt c₀ * (c₁ * x) ^ (5 / 4 : ℝ) := by gcongr
      _ = _ := by rw [Real.mul_rpow h₁.le hx]; ring

/-- A positive stretched-exponential exponent eventually dominates every
fixed multiple of the exponent in (4.2), even when the stretch depends on
the characteristic or the selected identity. -/
theorem log_rate_lt_power {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    ∀ᶠ n : ℕ in atTop, a * (Real.logb 2 n) ^ (5 / 4 : ℝ) < (n : ℝ) ^ ε := by
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C := (max a 0 + 1) / (Real.log 2) ^ (5 / 4 : ℝ)
  have hC : 0 < C := div_pos (by positivity) (Real.rpow_pos_of_pos h₂ _)
  have hO := ((isLittleO_log_rpow_rpow_atTop (5 / 4 : ℝ) hε).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound (show 0 < 1 / (2 * C) by positivity)
  filter_upwards [hO, eventually_ge_atTop (1 : ℕ)] with n hn hn₁
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn₁
  have hlog := Real.log_nonneg h1
  change ‖Real.log n ^ (5 / 4 : ℝ)‖ ≤ (1 / (2 * C)) * ‖(n : ℝ) ^ ε‖ at hn
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at hn
  have h := mul_le_mul_of_nonneg_left hn hC.le
  have hh : C * (1 / (2 * C)) = 1 / 2 := by field_simp
  rw [← mul_assoc, hh] at h
  have hnpos := Real.rpow_pos_of_pos (zero_lt_one.trans_le h1) ε
  calc
    _ ≤ (max a 0 + 1) * (Real.logb 2 n) ^ (5 / 4 : ℝ) := by
      exact mul_le_mul_of_nonneg_right ((le_max_left a 0).trans (le_add_of_nonneg_right zero_le_one))
        (Real.rpow_nonneg (Real.logb_nonneg (by norm_num) h1) _)
    _ = C * Real.log n ^ (5 / 4 : ℝ) := by
      rw [Real.logb, Real.div_rpow hlog h₂.le]; dsimp [C]; ring
    _ < _ := by linarith

/-- A single exceptional large length that yields a stretch estimate rules
out infinitely many exceptional lengths. This is the quantifier step on page 14. -/
theorem eventually_large_of_stretch {s : ℕ → ℝ} {a : ℝ}
    (stretch : (∃ᶠ n : ℕ in atTop, s n < 2 ^ (a * (Real.logb 2 n) ^ (5 / 4 : ℝ))) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((n : ℝ) ^ ε) ≤ s n) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ (a * (Real.logb 2 n) ^ (5 / 4 : ℝ)) ≤ s n := by
  by_contra h
  have hbad : ∃ᶠ n : ℕ in atTop, s n < 2 ^ (a * (Real.logb 2 n) ^ (5 / 4 : ℝ)) := by
    simpa only [Filter.Frequently, not_lt] using h
  obtain ⟨ε, hε, hstretch⟩ := stretch hbad
  apply h
  filter_upwards [hstretch, log_rate_lt_power hε a] with n hs hn
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hn.le).trans hs

end Crossing

end BorderVNP
end Computability
end OAI

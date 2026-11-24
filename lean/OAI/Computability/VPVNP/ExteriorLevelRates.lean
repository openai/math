import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Adjacent exterior dimensions

Appendix A, equation (A.2), of *VP and VNP differ over every field* chooses
three adjacent exterior powers of a `Q`-dimensional space. Rounding the real
level `(Q + 1) / (1 + x)` approximates the target adjacent-dimension ratios
`x` and `1 / x` within a factor of four, including the extreme levels.
-/

namespace OAI
namespace Computability
namespace VPVNP

open Filter
open scoped Topology

namespace ExteriorLevelRates

theorem choose_up_mul (Q b : ℕ) :
    Q.choose (b + 1) * (b + 1) = (Q - b) * Q.choose b := by
  simpa only [Nat.mul_comm (Q.choose b)] using Nat.choose_succ_right_eq Q b

theorem choose_down_mul {Q b : ℕ} (hb : 0 < b) (hQ : b ≤ Q) :
    Q.choose (b - 1) * (Q - b + 1) = b * Q.choose b := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  simpa only [Nat.add_one_sub_one, show Q - (a + 1) + 1 = Q - a by omega,
    Nat.mul_comm (a + 1)] using (Nat.choose_succ_right_eq Q a).symm

/-- The exact upward dimension ratio in (A.2). -/
theorem choose_up_ratio {Q b : ℕ} (hQ : b ≤ Q) :
    (Q.choose (b + 1) : ℝ) / Q.choose b = ((Q - b : ℕ) : ℝ) / (b + 1) := by
  have h : (0 : ℝ) < Q.choose b := by exact_mod_cast Nat.choose_pos hQ
  apply (div_eq_div_iff h.ne' (by positivity)).2
  exact_mod_cast choose_up_mul Q b

/-- The exact downward dimension ratio in (A.2). -/
theorem choose_down_ratio {Q b : ℕ} (hb : 0 < b) (hQ : b ≤ Q) :
    (Q.choose (b - 1) : ℝ) / Q.choose b = (b : ℝ) / (((Q - b : ℕ) : ℝ) + 1) := by
  have h : (0 : ℝ) < Q.choose b := by exact_mod_cast Nat.choose_pos hQ
  apply (div_eq_div_iff h.ne' (by positivity)).2
  exact_mod_cast choose_down_mul hb hQ

/-- The rounded level, capped to leave room for one more generator. -/
noncomputable def level (Q : ℕ) (x : ℝ) : ℕ :=
  min ⌊((Q : ℝ) + 1) / (1 + x)⌋₊ (Q - 1)

private theorem ratio_bounds {a b y z : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hy : b ≤ y) (hy' : y ≤ b + 1) (hz : a ≤ z) (hz' : z ≤ a + 1) :
    z / y / 4 ≤ a / (b + 1) ∧ a / (b + 1) ≤ z / y := by
  constructor
  · calc
      z / y / 4 = (z / 2) / (2 * y) := by ring
      _ ≤ a / (b + 1) := div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
  · exact div_le_div₀ (by linarith) hz (by linarith) hy'

/-- Both adjacent binomial ratios attain their target to within a factor of four. -/
theorem level_bounds {Q : ℕ} {x : ℝ} (hQ : 2 ≤ Q) (hlo : 1 / Q ≤ x) (hhi : x ≤ Q) :
    let b := level Q x
    let up := (Q.choose (b + 1) : ℝ) / Q.choose b
    let down := (Q.choose (b - 1) : ℝ) / Q.choose b
    1 ≤ b ∧ b < Q ∧ (x / 4 ≤ up ∧ up ≤ x) ∧ (x⁻¹ / 4 ≤ down ∧ down ≤ x⁻¹) := by
  let b := level Q x
  let y : ℝ := (Q + 1) / (1 + x)
  let z : ℝ := Q + 1 - y
  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hx : 0 < x := lt_of_lt_of_le (by positivity) hlo
  have hden : 0 < 1 + x := by linarith
  have hy : 1 ≤ y := (le_div_iff₀ hden).2 (by linarith)
  have hyQ : y ≤ Q := by
    have := (div_le_iff₀ (show 0 < (Q : ℝ) by linarith)).1 hlo
    exact (div_le_iff₀ hden).2 (by nlinarith)
  have hb : 1 ≤ b := le_min ((Nat.one_le_floor_iff y).2 hy) (by omega)
  have hbQ : b < Q := lt_of_le_of_lt (min_le_right _ _) (by omega)
  have hby : (b : ℝ) ≤ y := by
    exact (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le (by linarith))
  have hyb : y ≤ b + 1 := by
    by_cases h : ⌊y⌋₊ ≤ Q - 1
    · change y ≤ (min ⌊y⌋₊ (Q - 1) : ℕ) + (1 : ℝ)
      rw [min_eq_left h]
      exact (Nat.lt_floor_add_one y).le
    · change y ≤ (min ⌊y⌋₊ (Q - 1) : ℕ) + (1 : ℝ)
      rw [min_eq_right (by omega), Nat.cast_sub (by omega : 1 ≤ Q), Nat.cast_one]
      linarith
  have ha : (1 : ℝ) ≤ (Q - b : ℕ) := by exact_mod_cast (show 1 ≤ Q - b by omega)
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have haz : ((Q - b : ℕ) : ℝ) ≤ z := by
    rw [Nat.cast_sub hbQ.le]; dsimp [z]; linarith
  have hza : z ≤ ((Q - b : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub hbQ.le]; dsimp [z]; linarith
  have hxy : z / y = x := by
    apply (div_eq_iff (by linarith : y ≠ 0)).2
    have h : y * (1 + x) = Q + 1 := div_mul_cancel₀ _ hden.ne'
    dsimp [z]; nlinarith
  have hinv : y / z = x⁻¹ := by rw [← hxy, inv_div]
  refine ⟨hb, hbQ, ?_, ?_⟩
  · rw [choose_up_ratio hbQ.le, ← hxy]
    exact ratio_bounds ha hb' hby hyb haz hza
  · rw [choose_down_ratio hb hbQ.le, ← hinv]
    exact ratio_bounds hb' ha haz hza hby hyb

/-- The exterior level at tensor power `n` for a marked index of dimension `q`. -/
noncomputable def powerLevel (q : ℕ) (s : ℝ) (n : ℕ) : ℕ :=
  level (q ^ n) ((q : ℝ) ^ (s * n))

private theorem log_bounds {q v r : ℝ} (hq : 1 < q) (h : q ^ v / 4 ≤ r ∧ r ≤ q ^ v) :
    v - Real.logb q 4 ≤ Real.logb q r ∧ Real.logb q r ≤ v := by
  have hq' : 0 < q := by linarith
  have hp := Real.rpow_pos_of_pos hq' v
  have hlow := Real.logb_le_logb_of_le hq (by positivity) h.1
  have hhigh := Real.logb_le_logb_of_le hq (lt_of_lt_of_le (by positivity) h.1) h.2
  rw [Real.logb_div hp.ne' (by norm_num), Real.logb_rpow hq' hq.ne'] at hlow
  rw [Real.logb_rpow hq' hq.ne'] at hhigh
  exact ⟨hlow, hhigh⟩

/-- The error in each *unnormalized* logarithm is at most `logb q 4` for every positive `n`. -/
theorem powerLevel_log_bounds {q n : ℕ} {s : ℝ} (hq : 2 ≤ q) (hn : 1 ≤ n)
    (hs₀ : -1 ≤ s) (hs₁ : s ≤ 1) :
    let Q := q ^ n
    let b := powerLevel q s n
    let up := Real.logb q ((Q.choose (b + 1) : ℝ) / Q.choose b)
    let down := Real.logb q ((Q.choose (b - 1) : ℝ) / Q.choose b)
    1 ≤ b ∧ b < Q ∧
      (s * n - Real.logb q 4 ≤ up ∧ up ≤ s * n) ∧
      ((-s) * n - Real.logb q 4 ≤ down ∧ down ≤ (-s) * n) := by
  have hQ : 2 ≤ q ^ n := hq.trans (by simpa using Nat.pow_le_pow_right (by omega : 0 < q) hn)
  have hq' : (1 : ℝ) < q := by exact_mod_cast (show 1 < q from hq)
  have hq₀ : 0 < (q : ℝ) := by linarith
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlo := Real.rpow_le_rpow_of_exponent_le hq'.le (by nlinarith : -(n : ℝ) ≤ s * n)
  have hhi := Real.rpow_le_rpow_of_exponent_le hq'.le (by nlinarith : s * n ≤ (n : ℝ))
  rw [Real.rpow_neg hq₀.le, Real.rpow_natCast, ← Nat.cast_pow, ← one_div] at hlo
  rw [Real.rpow_natCast, ← Nat.cast_pow] at hhi
  obtain ⟨hb, hbQ, hup, hdown⟩ := level_bounds hQ hlo hhi
  refine ⟨hb, hbQ, log_bounds hq' hup, log_bounds hq' ?_⟩
  rwa [neg_mul, Real.rpow_neg hq₀.le]

private theorem tendsto_normalized_log {u : ℕ → ℝ} {s C : ℝ}
    (hu : ∀ n : ℕ, 1 ≤ n → s * n - C ≤ u n ∧ u n ≤ s * n) :
    Tendsto (fun n : ℕ ↦ u n / n) atTop (𝓝 s) := by
  have hl : Tendsto (fun n : ℕ ↦ s - C / n) atTop (𝓝 s) := by
    simpa only [sub_zero] using (tendsto_const_div_atTop_nhds_zero_nat C).const_sub s
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl (tendsto_const_nhds (x := s))
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from hn)
    rw [le_div_iff₀ hn', sub_mul, div_mul_cancel₀ _ hn'.ne']
    exact (hu n hn).1
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (div_le_iff₀ (by exact_mod_cast (show 0 < n from hn))).2 (hu n hn).2

/-- Equation (A.2) along `Q = q ^ n`, simultaneously for the two adjacent dimensions. -/
theorem exists_level_rates {q : ℕ} {s : ℝ} (hq : 2 ≤ q) (hs₀ : -1 ≤ s) (hs₁ : s ≤ 1) :
    ∃ b : ℕ → ℕ, (∀ n, 1 ≤ n → 1 ≤ b n ∧ b n < q ^ n) ∧
      Tendsto (fun n ↦ Real.logb q (((q ^ n).choose (b n + 1) : ℝ) / (q ^ n).choose (b n)) / n)
        atTop (𝓝 s) ∧
      Tendsto (fun n ↦ Real.logb q (((q ^ n).choose (b n - 1) : ℝ) / (q ^ n).choose (b n)) / n)
        atTop (𝓝 (-s)) := by
  refine ⟨powerLevel q s, fun n hn ↦ ?_, ?_, ?_⟩
  · have h := powerLevel_log_bounds hq hn hs₀ hs₁
    exact ⟨h.1, h.2.1⟩
  · exact tendsto_normalized_log fun n hn ↦ (powerLevel_log_bounds hq hn hs₀ hs₁).2.2.1
  · exact tendsto_normalized_log fun n hn ↦ (powerLevel_log_bounds hq hn hs₀ hs₁).2.2.2

/-- The three exterior dimensions used in (A.2) are all positive. -/
theorem choose_adjacent_pos {Q b : ℕ} (hb : 1 ≤ b) (hbQ : b < Q) :
    0 < Q.choose b ∧ 0 < Q.choose (b + 1) ∧ 0 < Q.choose (b - 1) :=
  ⟨Nat.choose_pos hbQ.le, Nat.choose_pos hbQ, Nat.choose_pos (by omega)⟩

/-- Exponentiating a normalized base-`q` logarithmic rate gives the limit of nth roots. -/
theorem tendsto_nthRoot_of_logb_rate {q : ℕ} (hq : 2 ≤ q) {x : ℕ → ℝ} {s : ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < x n)
    (hrate : Tendsto (fun n : ℕ ↦ Real.logb q (x n) / n) atTop (𝓝 s)) :
    Tendsto (fun n : ℕ ↦ (x n) ^ (n : ℝ)⁻¹) atTop (𝓝 ((q : ℝ) ^ s)) := by
  have hq_one : (1 : ℝ) < q := by exact_mod_cast (show 1 < q from hq)
  have hq_pos := zero_lt_one.trans hq_one
  apply ((Real.continuousAt_const_rpow hq_pos.ne').tendsto.comp hrate).congr'
  filter_upwards [hpos] with n hn
  change (q : ℝ) ^ (Real.logb q (x n) / n) = (x n) ^ (n : ℝ)⁻¹
  rw [div_eq_mul_inv, Real.rpow_mul hq_pos.le, Real.rpow_logb hq_pos hq_one.ne' hn]

end ExteriorLevelRates

end VPVNP
end Computability
end OAI

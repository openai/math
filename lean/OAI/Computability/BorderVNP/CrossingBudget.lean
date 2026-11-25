import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Balanced cuts and the selector cost

In Section 4.4 the first crossing tensor has (D) terminal indices and (p)
bridge indices. A balanced cut splits these into two groups. Once (D ≥ 441),
the bound (p ≤ 1.05 √D) ensures that one group can pay for its bridge wires
after the junction moves. The final estimate also pays for broadcasting the
choice of a summand to all (2D) terminals.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

private theorem bridge_le_twentieth {D p : ℕ} (hD : 441 ≤ D)
    (hp : (p : ℝ) ≤ 21 / 20 * Real.sqrt D) : (p : ℝ) ≤ D / 20 := by
  have h : 21 ≤ Real.sqrt D := Real.le_sqrt_of_sq_le (by norm_num; exact_mod_cast hD)
  nlinarith only [hp, mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg (D : ℝ)),
    Real.mul_self_sqrt (Nat.cast_nonneg D)]

/-- Both groups in a balanced cut contain between thirty and seventy percent of the terminals. -/
theorem balanced_terminal_range {D p s b : ℕ} (hD : 441 ≤ D)
    (hp : (p : ℝ) ≤ 21 / 20 * Real.sqrt D) (hb : b ≤ p)
    (hlo : D + p ≤ 3 * (s + b)) (hhi : 3 * (s + b) ≤ 2 * (D + p)) :
    3 / 10 * (D : ℝ) ≤ s ∧ (s : ℝ) ≤ 7 / 10 * D := by
  have hlo' : (D : ℝ) + p ≤ 3 * (s + (b : ℝ)) := by exact_mod_cast hlo
  have hhi' : 3 * ((s : ℝ) + b) ≤ 2 * ((D : ℝ) + p) := by exact_mod_cast hhi
  have hb' : (b : ℝ) ≤ p := by exact_mod_cast hb
  have h := bridge_le_twentieth hD hp
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) b]

private theorem balanced_sqrt_sum {D s r : ℝ} (hD : 0 < D) (h : s + r = D)
    (hs : 3 / 10 * D ≤ s) (hr : 3 / 10 * D ≤ r) :
    13 / 10 * Real.sqrt D < Real.sqrt s + Real.sqrt r := by
  have hs₀ : 0 ≤ s := by linarith
  have hr₀ : 0 ≤ r := by linarith
  have hprod : 2 / 5 * D ≤ Real.sqrt s * Real.sqrt r := by
    rw [← Real.sqrt_mul hs₀]
    apply Real.le_sqrt_of_sq_le
    nlinarith only [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hr),
      congrArg (D * ·) h, sq_nonneg D]
  apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
  nlinarith only [hD, h, hprod, Real.sq_sqrt hD.le, Real.sq_sqrt hs₀, Real.sq_sqrt hr₀]

/-- Either a balanced group or its complement satisfies the displacement margin (4.4). -/
theorem balanced_cut_side {D p s b : ℕ} (hD : 441 ≤ D)
    (hp : (p : ℝ) ≤ 21 / 20 * Real.sqrt D) (hs : s ≤ D) (hb : b ≤ p)
    (hlo : D + p ≤ 3 * (s + b)) (hhi : 3 * (s + b) ≤ 2 * (D + p)) :
    1 / 10 * Real.sqrt D ≤ Real.sqrt s - b ∨
      1 / 10 * Real.sqrt D ≤ Real.sqrt (D - s : ℕ) - (p - b : ℕ) := by
  obtain ⟨hlo', hhi'⟩ := balanced_terminal_range hD hp hb hlo hhi
  rw [Nat.cast_sub hs, Nat.cast_sub hb]
  have hd : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have h := balanced_sqrt_sum hd (show (s : ℝ) + (D - s) = D by ring) hlo' (by linarith)
  by_cases hside : 1 / 10 * Real.sqrt D ≤ Real.sqrt s - b
  · exact Or.inl hside
  · right
    linarith [Real.sqrt_nonneg (D : ℝ)]

/-- Rounding the rank index in (4.3) to an integral bit width costs at most one bit. -/
theorem rankBits_le {R m D : ℕ} (hlarge : 100 ≤ (m : ℝ) * Real.sqrt D)
    (hrank : (R : ℝ) ≤ (2 : ℝ) ^ (1 / 50 * m * Real.sqrt D)) :
    (Nat.clog 2 R : ℝ) ≤ 3 / 100 * m * Real.sqrt D := by
  rcases R with _ | R
  · simp
    positivity
  have hpos : 0 < ((R + 1 : ℕ) : ℝ) := by positivity
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpos hrank
  rw [Real.logb_rpow (by norm_num) (by norm_num)] at hlog
  rw [← Real.natCeil_logb_natCast]
  have hr : 0 ≤ Real.logb 2 ((R + 1 : ℕ) : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le R))
  have hc := Nat.ceil_lt_add_one hr
  linarith

/-- The term word broadcast in (3.1) costs less than the displacement saves. The
bound on the number of terms counts both the crossing choices and the balanced cuts. -/
theorem strict_selector_budget {m D p L : ℕ} {c₀ w : ℝ} (hm : 0 < m) (hD : 441 ≤ D)
    (hp : (p : ℝ) ≤ 21 / 20 * Real.sqrt D)
    (hc : 6 * c₀ ^ 2 < 1 / 500) (hdir : (D : ℝ) ≤ c₀ * Real.sqrt m)
    (hL : L ≤ 2 ^ (D + (D + p))) (hLpos : 0 < L)
    (hw : w ≤ 2 * D * m - m / 500) :
    w + 2 * D * Real.logb 2 L < 2 * D * m := by
  have hpm : p ≤ D := by
    have h : (p : ℝ) ≤ D := by linarith [bridge_le_twentieth hD hp, Nat.cast_nonneg (α := ℝ) D]
    exact_mod_cast h
  have hpow : (L : ℝ) ≤ (2 : ℝ) ^ (3 * D) := by
    exact_mod_cast hL.trans (Nat.pow_le_pow_right (by decide : 0 < 2)
      (show D + (D + p) ≤ 3 * D by omega))
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (show (0 : ℝ) < L by exact_mod_cast hLpos) hpow
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hlog
  push_cast at hlog
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) D) hdir 2
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)] at hsq
  have hbudget := mul_lt_mul_of_pos_right hc (show (0 : ℝ) < m by exact_mod_cast hm)
  nlinarith only [hw, hbudget, hsq, mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) D)]

end Crossing

end BorderVNP
end Computability
end OAI

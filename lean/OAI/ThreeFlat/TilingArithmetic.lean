import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI
/-! # Selector and residual-width bounds for repeated tiles -/

namespace ThreeFlat

open Filter

/-- Splitting a large width into whole tiles and one remainder keeps the total selector
rate and the per-pair slack below the prescribed budgets. -/
theorem eventually_tiling_budgets {q b s : ℕ} {ε η : ℝ}
    (hq : 0 < q) (hb : 0 < b) (hε : 0 < ε) (hη : 0 < η) (hεq : 1 ≤ ε * q)
    (hs : (s : ℝ) ≤ η*b) :
    ∀ᶠ v : ℕ in atTop,
      let t := v / (4*q*b)
      let r := v % (4*q*b)
      4*q*b*t+r = v ∧ ((s*t : ℕ) : ℝ) ≤ η*v ∧ ((2*b*t+r : ℕ) : ℝ) ≤ ε*v := by
  let m := 4*q*b
  have hm : 0 < m := by dsimp [m]; positivity
  obtain ⟨N,hN⟩ := exists_nat_ge (2*(m:ℝ)/ε)
  filter_upwards [eventually_ge_atTop N] with v hv
  let t := v / m
  let r := v % m
  change m*t+r = v ∧ _ ∧ _
  have split : m*t+r = v := Nat.div_add_mod v m
  have hr : r ≤ m := (Nat.mod_lt v hm).le
  have hwhole : m*t ≤ v := by omega
  have hbt : b*t ≤ v :=
    (Nat.mul_le_mul_right t (Nat.le_mul_of_pos_left b (show 0 < 4*q by positivity))).trans hwhole
  have hbudget : (2:ℝ)*m ≤ ε*v := by
    have h := (div_le_iff₀ hε).mp (hN.trans (show (N:ℝ) ≤ v by exact_mod_cast hv))
    linarith
  have htprice := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg t (α := ℝ))
  have hwholePrice := mul_le_mul_of_nonneg_left (show ((b*t:ℕ):ℝ) ≤ v by exact_mod_cast hbt) hη.le
  have hst : ((s*t:ℕ):ℝ) ≤ η*v := by
    push_cast at hwholePrice ⊢
    linarith only [htprice, hwholePrice]
  have wholeCap := mul_le_mul_of_nonneg_left (show ((m*t:ℕ):ℝ) ≤ v by exact_mod_cast hwhole) hε.le
  have useCap := mul_le_mul_of_nonneg_right hεq (show 0 ≤ 4*(b:ℝ)*t by positivity)
  have hr' : (r:ℝ) ≤ m := by exact_mod_cast hr
  refine ⟨split,hst,?_⟩
  change ((2*b*t+r:ℕ):ℝ) ≤ ε*v
  dsimp [m] at wholeCap hbudget hr'
  push_cast at wholeCap hbudget hr' ⊢
  linarith only [wholeCap, useCap, hbudget, hr']

end ThreeFlat

end OAI

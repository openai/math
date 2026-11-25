import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI
/-! # Integer capacities for the two concentrator passes

For at most `C * R` possible requests and slack at least `1 / q`, put
`K = 4 C q`. Each reserve vertex gets `⌊D/K⌋` slots. The greedy residual
threshold is `⌊C R / (16 K²)⌋`.
-/

namespace ThreeFlat.Concentrator

/-- Replace real slack by an integral reciprocal valid at every capacity. -/
theorem exists_slack_denominator {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, 0 < q ∧ ∀ R active : ℕ, (active : ℝ) ≤ (1 - ε) * R →
      q * active + R ≤ q * R := by
  obtain ⟨q, hq⟩ := exists_nat_gt (1 / ε)
  have hq' : (0 : ℝ) < q := (one_div_pos.mpr hε).trans hq
  have scaled : 1 ≤ (q : ℝ) * ε := ((div_lt_iff₀ hε).mp hq).le
  refine ⟨q, by exact_mod_cast hq', ?_⟩
  intro R active legal
  have act := mul_le_mul_of_nonneg_left legal hq'.le
  have slack := mul_le_mul_of_nonneg_right scaled (Nat.cast_nonneg (α := ℝ) R)
  exact_mod_cast (show (q : ℝ) * active + R ≤ q * R by linarith only [act, slack])

def budgetDenom (C q : ℕ) := 4 * C * q

def reserveSlots (C q D : ℕ) := D / budgetDenom C q

def reserveThreshold (C q R : ℕ) := C * R / (16 * (budgetDenom C q) ^ 2)

theorem reserve_capacity {C q R m D : ℕ} (hC : 0 < C) (hq : 0 < q)
    (scale : m * D ≤ 2 * C * R) :
    q * (m * reserveSlots C q D + reserveThreshold C q R) ≤ R := by
  let K := budgetDenom C q
  have hK : 0 < K := by dsimp [K, budgetDenom]; positivity
  have hfactor : K ≤ 16 * K ^ 2 := by nlinarith [Nat.mul_le_mul_right K (show 1 ≤ K by omega)]
  have hslots : K * (D / K) ≤ D := Nat.mul_div_le ..
  have hthresh : K * reserveThreshold C q R ≤ C * R :=
    (Nat.mul_le_mul_right _ hfactor).trans (Nat.mul_div_le ..)
  apply Nat.le_of_mul_le_mul_left (c := 4 * C) _ (by positivity)
  calc
    4 * C * (q * (m * reserveSlots C q D + reserveThreshold C q R)) =
      m * (K * (D / K)) + K * reserveThreshold C q R := by
        dsimp [reserveSlots, K, budgetDenom]; ring
    _ ≤ m * D + C * R := Nat.add_le_add (Nat.mul_le_mul_left m hslots) hthresh
    _ ≤ 4 * C * R := by nlinarith

/-- The total public slot count pays for both the reserve and the slack
required by the greedy pass. -/
theorem greedy_bank_slack {C q R m D active : ℕ} (hC : 0 < C) (hq : 0 < q)
    (scale : m * D ≤ 2 * C * R) (legal : q * active + R ≤ q * R) :
    active + reserveThreshold C q R + m * reserveSlots C q D ≤ R := by
  have room := reserve_capacity hC hq scale
  apply Nat.le_of_mul_le_mul_left (c := q) _ hq
  nlinarith only [legal, room]

theorem threshold_density {C q R : ℕ} (hC : 0 < C) (hq : 0 < q)
    (large : 16 * (budgetDenom C q) ^ 2 ≤ C * R) :
    (1 / (32 * (budgetDenom C q : ℝ) ^ 2)) * (C * R : ℕ) ≤ (reserveThreshold C q R : ℝ) := by
  let t := reserveThreshold C q R
  let a := 16 * (budgetDenom C q) ^ 2
  have ha : 0 < a := by dsimp [a, budgetDenom]; positivity
  have ht : 0 < t := Nat.div_pos large ha
  have less : C * R < a * (t + 1) := Nat.lt_mul_div_succ _ ha
  have small : C * R ≤ a * (2 * t) :=
    less.le.trans (Nat.mul_le_mul_left _ (by omega))
  have cast : (C * R : ℕ) ≤ (16 * (budgetDenom C q : ℝ) ^ 2) * (2 * (t : ℝ)) := by
    exact_mod_cast small
  have hk : (0 : ℝ) < budgetDenom C q := by unfold budgetDenom; positivity
  rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
  change (C * R : ℕ) ≤ (t : ℝ) * (32 * (budgetDenom C q : ℝ) ^ 2)
  linarith only [cast]

/-- The halving condition holds with the integer number of slots at each
vertex, including the loss from rounding down. -/
theorem reserve_sparse_budget {C q R m D : ℕ} (hC : 0 < C) (hq : 0 < q)
    (hm : 0 < m) (hD : 0 < D) (scale : C * R ≤ m * D) {lam : ℝ}
    (spectral : lam ≤ 1 / (8 * (budgetDenom C q : ℝ))) :
    4 * (D : ℝ) * (2 * (reserveThreshold C q R : ℝ) /
      (((reserveSlots C q D : ℝ) + 1) * m) + lam) ≤ (reserveSlots C q D : ℝ) + 1 := by
  let K : ℝ := budgetDenom C q
  let T : ℝ := reserveThreshold C q R
  let S : ℝ := (reserveSlots C q D : ℝ) + 1
  have hk : (0 : ℕ) < budgetDenom C q := by unfold budgetDenom; positivity
  have hK : 0 < K := by dsimp only [K]; exact_mod_cast hk
  have hS : 0 < S := by dsimp [S]; positivity
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hTnat : 16 * (budgetDenom C q) ^ 2 * reserveThreshold C q R ≤ m * D :=
    (Nat.mul_div_le ..).trans scale
  have hT : 16 * K ^ 2 * T ≤ (m : ℝ) * D := by dsimp only [K, T]; exact_mod_cast hTnat
  have hSnat : D ≤ budgetDenom C q * (reserveSlots C q D + 1) :=
    (Nat.lt_mul_div_succ _ hk).le
  have hSF : (D : ℝ) ≤ K * S := by dsimp only [K, S]; exact_mod_cast hSnat
  have density : 2 * T / (S * m) ≤ 1 / (8 * K) := by
    rw [div_le_div_iff₀ (mul_pos hS hm') (by positivity)]
    apply (mul_le_mul_iff_left₀ hK).mp
    calc
      2 * T * (8 * K) * K = 16 * K ^ 2 * T := by ring
      _ ≤ (m : ℝ) * D := hT
      _ ≤ m * (K * S) := mul_le_mul_of_nonneg_left hSF hm'.le
      _ = 1 * (S * m) * K := by ring
  change 4 * (D : ℝ) * (2 * T / (S * m) + lam) ≤ S
  calc
    _ ≤ 4 * (D : ℝ) * (1 / (8 * K) + 1 / (8 * K)) :=
      mul_le_mul_of_nonneg_left (add_le_add density spectral) (by positivity)
    _ = D / K := by field_simp; ring
    _ ≤ S := (div_le_iff₀ hK).mpr (by simpa only [mul_comm K] using hSF)

end ThreeFlat.Concentrator

end OAI

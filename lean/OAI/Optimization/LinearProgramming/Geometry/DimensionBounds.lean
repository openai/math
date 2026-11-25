import OAI.Optimization.LinearProgramming.Compression.BitBudget
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! Numeric clocks evaluated on the matrix dimensions. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Compression

/-- An integer-only upper bound on the number of restarts. -/
def minorRestartBudget (n : ℕ) : ℕ := (7*n^2 + 8) * ((n+1).log2 + 1)

theorem ceil_minorCap_le_budget (n : ℕ) :
    ⌈(7*(n:ℝ)^2+8) * Real.logb 2 (n+1)⌉₊ ≤ minorRestartBudget n := by
  have hp : (n+1 : ℝ) ≤ (2 : ℝ)^((n+1).log2+1 : ℕ) := by exact_mod_cast (n+1).lt_log2_self.le
  have hlog : Real.logb 2 ((n:ℝ)+1) ≤ (((n+1).log2+1 : ℕ) : ℝ) := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (by positivity)).mpr
    simpa only [Real.rpow_natCast] using hp
  apply Nat.ceil_le.mpr
  simpa only [minorRestartBudget, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
    mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 7*(n:ℝ)^2+8)

/-- The integer restart clock itself is bounded by a dimension-only polynomial. -/
theorem minorRestartBudget_le (n : ℕ) : minorRestartBudget n ≤ 15*(n+2)^3 := by
  have h := Nat.succ_le_succ (Nat.log2_le_self (n+1))
  calc
    minorRestartBudget n ≤ (7*n^2+8)*(n+2) := Nat.mul_le_mul_left _ h
    _ ≤ 15*(n+2)^3 := by nlinarith

/-- Explicit dimension-only range of the compressed hidden costs, evaluated by natural
arithmetic rather than by traversing the support of a formal polynomial. -/
def minorCostMagnitude (n : ℕ) : ℕ := 2 ^ onlineMinorBitFormula n

theorem minorCostMagnitude_eq (n : ℕ) : minorCostMagnitude n = 2 ^ onlineMinorBitPolynomial.eval n := by
  rw [onlineMinorBitPolynomial_eval, minorCostMagnitude]

/-- Numeric clock evaluated before the first query, independently of coefficient sizes. -/
def subspaceQueryClock (n : ℕ) : ℕ := (n + onlineMinorBitFormula n + 3)^1510

theorem twice_minorCostMagnitude_size (n : ℕ) : (2 * minorCostMagnitude n).size = onlineMinorBitFormula n + 2 := by
  rw [minorCostMagnitude, ← pow_succ', Nat.size_pow]

private noncomputable def queryCostPolynomial (p : Polynomial ℕ) (exponent : ℕ) : Polynomial ℕ :=
  (15*(Polynomial.X+2)^3 + 1) * ((Polynomial.X+p+3)^exponent + 1) * Polynomial.X^2

private theorem queryCostPolynomial_eval (p : Polynomial ℕ) (exponent n : ℕ) :
    (queryCostPolynomial p exponent).eval n = (15*(n+2)^3+1) * ((n+p.eval n+3)^exponent+1) * n^2 := by
  simp only [queryCostPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]

/-- A single fixed polynomial bounds physical minor requests for every rational input
matrix pair. It counts the minor that triggers each discarded partial price query. -/
noncomputable def subspaceMinorCallsPolynomial : Polynomial ℕ := queryCostPolynomial onlineMinorBitPolynomial 1510

theorem subspaceMinorCalls_bound (r n : ℕ) (hr : r ≤ n) :
    (minorRestartBudget n + 1) * (subspaceQueryClock n + 1) * (r*n) ≤ subspaceMinorCallsPolynomial.eval n := by
  have hrn : r*n ≤ n^2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ hr
  rw [subspaceMinorCallsPolynomial, queryCostPolynomial_eval, onlineMinorBitPolynomial_eval, subspaceQueryClock]
  exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.add_le_add_right (minorRestartBudget_le n) 1)) hrn

end Geometry
end LinearProgramming
end Optimization
end OAI

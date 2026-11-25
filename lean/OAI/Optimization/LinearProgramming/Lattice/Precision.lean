import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! Explicit precision and radix sizes for the sign-oracle computation. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

/-- Logarithmic scale of the rational simultaneous-approximation call. -/
def precisionExponent (p M : ℕ) : ℕ := 4 * (p + 1) + M.size + 6

def searchDenominator (p M : ℕ) : ℕ := 2 ^ precisionExponent p M

/-- Dyadic queries per normalized coordinate. -/
def searchPrecision (p M : ℕ) : ℕ := precisionExponent p M * (p + 2)

/-- Bits per radix digit. This polynomial is written in dimension and input bit length. -/
def radixWidth (p M : ℕ) : ℕ := M.size + precisionExponent p M * (p + 1) + 3

theorem searchDenominator_pos (p M : ℕ) : 0 < searchDenominator p M := by
  exact pow_pos (by decide : 0 < 2) _

theorem searchDenominator_ge (p M : ℕ) : 8 * p * M ≤ searchDenominator p M := by
  calc
    8 * p * M ≤ 2^3 * 2^p * 2^M.size :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 8 Nat.lt_two_pow_self.le) (Nat.lt_size_self M).le
    _ = 2^(3 + p + M.size) := by rw [pow_add, pow_add]
    _ ≤ searchDenominator p M := Nat.pow_le_pow_right (by decide) (by unfold precisionExponent; omega)

theorem two_pow_searchPrecision (p M : ℕ) :
    2 ^ searchPrecision p M = searchDenominator p M ^ (p + 2) := by
  exact pow_mul _ _ _

theorem digit_bounds (p M : ℕ) :
    searchDenominator p M ^ (p + 1) + 1 < 2 ^ radixWidth p M ∧
      M * (searchDenominator p M ^ (p + 1) + 1) < 2 ^ radixWidth p M := by
  let e := precisionExponent p M
  have hq : searchDenominator p M ^ (p + 1) = 2 ^ (e * (p + 1)) := (pow_mul ..).symm
  have hD : searchDenominator p M ^ (p + 1) + 1 ≤ 2 ^ (e * (p + 1) + 1) := by
    rw [hq, pow_succ]
    have := Nat.one_le_two_pow (n := e * (p + 1))
    omega
  have h : M * (searchDenominator p M ^ (p + 1) + 1) ≤ 2 ^ (M.size + (e * (p + 1) + 1)) := by
    calc
      _ ≤ 2 ^ M.size * 2 ^ (e * (p + 1) + 1) := Nat.mul_le_mul (Nat.lt_size_self M).le hD
      _ = _ := (pow_add ..).symm
  constructor
  · exact hD.trans_lt (Nat.pow_lt_pow_right (by decide) (by dsimp [radixWidth, e]; omega))
  · exact h.trans_lt (Nat.pow_lt_pow_right (by decide) (by dsimp [radixWidth, e]; omega))

end Lattice
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.Geometry.FrankWolfe
import OAI.Optimization.LinearProgramming.RAM.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! A common denominator for the rational projector and the encoding width of
the polynomially bounded Frank–Wolfe iterates. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix Finset RAM
open scoped BigOperators Matrix

variable {n : ℕ}

theorem log2_le_of_le_two_pow {x k : ℕ} (h : x ≤ 2 ^ k) : x.log2 ≤ k := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · exact Nat.le_of_lt_succ <| (Nat.log2_lt hx.ne').mpr
      (h.trans_lt (by rw [pow_succ]; have := Nat.two_pow_pos k; omega))

/-- A common denominator for the residual matrix used by all Frank--Wolfe iterates. -/
def matrixDenominator (Q : Matrix (Fin n) (Fin n) ℚ) : ℕ := ∏ i, ∏ j, (Q i j).den

theorem matrixDenominator_pos (Q : Matrix (Fin n) (Fin n) ℚ) : 0 < matrixDenominator Q :=
  Finset.prod_pos (fun i _ => Finset.prod_pos (fun j _ => (Q i j).pos))

theorem den_dvd_matrixDenominator (Q : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (Q i j).den ∣ matrixDenominator Q :=
  (dvd_prod_of_mem (fun k => (Q i k).den) (mem_univ j)).trans
    (dvd_prod_of_mem (fun a => ∏ k, (Q a k).den) (mem_univ i))

theorem matrixDenominator_bound (Q : Matrix (Fin n) (Fin n) ℚ) {B : ℕ}
    (hb : ∀ i j, ratBits (Q i j) ≤ B) : matrixDenominator Q ≤ 2^(B*n*n) := by
  have hd i j : (Q i j).den ≤ 2^B := by
    have := hb i j
    unfold ratBits at this
    exact Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  calc
    matrixDenominator Q ≤ ∏ _i : Fin n, ∏ _j : Fin n, 2^B := by
      apply prod_le_prod (fun i _ => prod_le_prod (fun j _ => hd i j))
    _ = 2^(B*n*n) := by simp [pow_mul]

/-- Convert common-denominator/magnitude estimates to the actual rational register
encoding without interpreting an exponentially large denominator as a running time. -/
theorem fwBounded_ratBits {d m k : ℕ} {x : ℚ} (hd : 0 < d) (hdk : d ≤ 2^k)
    (h : FWBounded d (m : ℚ) x) : ratBits x ≤ 3 + m + 2*k := by
  obtain ⟨hden, hnum⟩ := fwBounded_encoding hd h
  have hm : x.num.natAbs ≤ 2^(m+k) := by
    rw [pow_add]; exact hnum.trans (Nat.mul_le_mul m.lt_two_pow_self.le hdk)
  have h₁ := log2_le_of_le_two_pow hm
  have h₂ := log2_le_of_le_two_pow (hden.trans hdk)
  unfold ratBits
  omega

end Geometry
end LinearProgramming
end Optimization
end OAI

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Support

/-! Convert a polynomial operation or encoding budget to the public RAM envelope `C(n+1)^k`. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

/-- Coefficient sum at one bounds every evaluation after factoring out the largest power. -/
theorem polynomial_eval_le_monomial (P : Polynomial ℕ) (n : ℕ) :
    P.eval n ≤ P.eval 1 * (n+1)^P.natDegree := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  simp only [Polynomial.sum, one_pow, mul_one, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  apply Nat.mul_le_mul_left
  exact (Nat.pow_le_pow_left (Nat.le_succ n) i).trans
    (Nat.pow_le_pow_right (Nat.succ_pos n) (Polynomial.le_natDegree_of_mem_supp i hi))

/-- The constant overhead for a canonical reduced signed rational fits the same degree. -/
theorem rat_width_monomial (P : Polynomial ℕ) (n : ℕ) :
    3+2*P.eval n ≤ (3+2*P.eval 1)*(n+1)^P.natDegree := by
  have h := polynomial_eval_le_monomial P n
  have hp : 0 < (n+1)^P.natDegree := pow_pos (Nat.succ_pos _) _
  rw [add_mul, Nat.mul_assoc]
  omega

end Compression
end LinearProgramming
end Optimization
end OAI

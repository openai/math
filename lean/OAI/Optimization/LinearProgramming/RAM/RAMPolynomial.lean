import OAI.Optimization.LinearProgramming.RAM.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM

/-- Evaluating any natural-coefficient time polynomial fits the public RAM bound. -/
theorem polynomial_eval_le_polyBound (p : Polynomial Nat) (n : Nat) :
    p.eval n ≤ polyBound (p.eval 1) p.natDegree n := by
  unfold polyBound
  rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum]
  simp only [Polynomial.sum,one_pow,mul_one,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  apply Nat.mul_le_mul_left
  exact (Nat.pow_le_pow_left (Nat.le_succ n) i).trans
    (Nat.pow_le_pow_right (Nat.succ_pos n) (Polynomial.le_natDegree_of_mem_supp i hi))

end RAM
end LinearProgramming
end Optimization
end OAI

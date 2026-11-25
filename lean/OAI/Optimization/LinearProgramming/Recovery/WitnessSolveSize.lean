import Mathlib.Algebra.Polynomial.Eval.Defs
import Lean.Elab.Tactic.Omega

/-! Dimension-only clocks and numeric height bounds for a rectangular solver call. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessSolve

open Polynomial

def solverTime (d m : ℕ) : ℕ := 10_000_000_000*(d+m+1)^9
def callTime (d m cap : ℕ) : ℕ := 19*cap+225+(2*solverTime d m+2)
def solverHeight (inputBits : ℕ) : ℕ := 1_000_000*(inputBits+1)^6

noncomputable def normalizedCallPolynomial : Polynomial ℕ :=
  19*((X+1)^2+2)+225+(2*10_000_000_000*(2*X+2)^9+2)

noncomputable def heightPolynomial : Polynomial ℕ := X+1_000_000*((X+1)^3+1)^6

theorem normalized_call_bound (h n : ℕ) :
    callTime n (h+n+1) ((n+1)*(h+n+1)+2) ≤ normalizedCallPolynomial.eval (h+n) := by
  simp only [normalizedCallPolynomial,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat]
  unfold callTime solverTime
  have area : (n+1)*(h+n+1) ≤ (h+n+1)^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right _ (by omega)
  have dims : n+(h+n+1)+1 ≤ 2*(h+n)+2 := by omega
  have pow := Nat.pow_le_pow_left dims 9
  omega

theorem old_height_le (h n e : ℕ) : e ≤ heightPolynomial.eval (h+n+e) := by
  simp only [heightPolynomial,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat]
  omega

end WitnessSolve
end Recovery
end LinearProgramming
end Optimization
end OAI

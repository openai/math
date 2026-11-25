import OAI.Optimization.LinearProgramming.RAM.TermBounds
import OAI.Optimization.LinearProgramming.PrimalDual.JointCell
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Data.Fin.VecNotation

/-! A fixed polynomial bounds every joint-instance coefficient/RHS query, independently
of the base addresses of both buffers and the input coefficients. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace JointRAM

open RAM RAM.Tape Polynomial

private def smallEnv (m d r j : Nat) : Env := ![m,d,0,0,r,j,0,0,0]

/-- Buffer addresses and work counters have no effect on the instruction envelope. -/
private theorem entryCost_eq (e : Env) :
    entry.cost e 2 = entry.cost (smallEnv (e 0) (e 1) (e 4) (e 5)) 2 := rfl

/-- An explicit fixed polynomial controls the cost of the emitted fixed cell program. -/
noncomputable def cellPolynomial : Polynomial Nat := entry.boundCost.comp (2*X+1)+2

theorem cell_cost (env : Env) (hr : env 4 < 2*env 0+2*env 1+1) (hj : env 5 ≤ env 1+env 0) :
    entry.cost env 2 + 2 ≤ cellPolynomial.eval (env 0+env 1) := by
  rw [entryCost_eq]
  have he : ∀ i, smallEnv (env 0) (env 1) (env 4) (env 5) i ≤ 2*(env 0+env 1)+1 := by
    intro i
    fin_cases i <;> simp [smallEnv] <;> omega
  simpa [cellPolynomial,Polynomial.eval_comp] using Nat.add_le_add_right (entry.cost_le _ 2 he) 2

end JointRAM
end PrimalDual
end LinearProgramming
end Optimization
end OAI

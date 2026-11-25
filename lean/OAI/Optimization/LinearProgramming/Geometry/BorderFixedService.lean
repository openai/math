import OAI.Optimization.LinearProgramming.Geometry.BorderService
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! The concrete initializer, service program and polynomial bounds chosen
before a pair of matrices is supplied. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM OracleSpec.MinorLog

def FixedServiceAt (init serve : Program) (B : Polynomial ℕ) (Cr : ℕ) {r s : ℕ}
    (D : Matrix (Fin r) (Fin (r+s)) ℚ) (E : Matrix (Fin s) (Fin (r+s)) ℚ) : Prop :=
  ∃ S : Service D E,
    S.program = serve ∧ S.clock = B.eval (r+s) ∧ S.outputBits = B.eval (r+s) ∧
    S.height = B.eval (totalBits (entries D++entries E)) ∧
    S.restartBudget = Cr*(r+s)^2*((2*(r+s)).log2+1) ∧
    call init S.clock S.height (start [r,s,r+s] (entries D++entries E)) S.ready ∧
    S.ready.output = some 0

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI

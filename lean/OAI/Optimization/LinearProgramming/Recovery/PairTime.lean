import OAI.Optimization.LinearProgramming.Recovery.PairBuilderProgram
import OAI.Optimization.LinearProgramming.Recovery.PairTimePolynomial

/-! Polynomial runtime witness of the fixed complementary-pair recovery ROM. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PairBuilder

noncomputable def timePolynomial : Polynomial ℕ := timePolynomialFor codeReserve metaBudget

theorem time_le_eval {h n : ℕ} (l : Layout h n) :
    time l ≤ timePolynomial.eval (h+n+l.scratch+l.previous) :=
  timePolynomialFor_bound codeReserve metaBudget h n l.scratch l.previous

end PairBuilder
end Recovery
end LinearProgramming
end Optimization
end OAI

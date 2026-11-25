import OAI.Optimization.LinearProgramming.Feasibility
import OAI.Optimization.LinearProgramming.PrimalDual.FrameOptimization

/-! Corollary 1.2 of *A strongly polynomial algorithm for linear programming*. -/

namespace OAI
namespace Optimization
namespace LinearProgramming

/-- A fixed rational RAM certifies infeasibility, returns a primal–dual optimum, or
returns a feasible point and a normalized improving ray. Its step bound depends only
on the dimensions, and every scalar has bit length polynomial in the input size. -/
theorem strongly_polynomial_optimization : StronglyPolynomialOptimization :=
  PrimalDual.stronglyPolynomialOptimization_of_feasibility strongly_polynomial_feasibility

end LinearProgramming
end Optimization
end OAI

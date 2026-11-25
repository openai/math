import OAI.Optimization.LinearProgramming.Recovery.PrincipalProgram
import OAI.Optimization.LinearProgramming.NormalSubspace.Unconditional

/-! Theorem 1.1 of *A strongly polynomial algorithm for linear programming*. -/

namespace OAI
namespace Optimization
namespace LinearProgramming

/-- A fixed rational RAM finds a feasible point or a sparse Farkas certificate.
Its running time is polynomial in the dimensions, and every scalar has bit length
polynomial in the encoded input size. -/
theorem strongly_polynomial_feasibility : StronglyPolynomialFeasibility := by
  obtain ⟨subspace⟩ := NormalSubspace.normal_decision
  exact Recovery.Principal.feasibility_of_subspace subspace

end LinearProgramming
end Optimization
end OAI

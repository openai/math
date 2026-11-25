import OAI.Optimization.LinearProgramming.Feasibility
import OAI.Optimization.LinearProgramming.PrimalDual.UniformCalls

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

/-- Corollary 1.2 with the strongly polynomial rational feasibility program of
Theorem 1.1 installed at both designated sites of a single optimization RAM. -/
theorem strong_two_calls : SubroutineCalls.StrongTwoCalls :=
  SubroutineCalls.strong_two_calls_of_feasibility strongly_polynomial_feasibility

end PrimalDual
end LinearProgramming
end Optimization
end OAI

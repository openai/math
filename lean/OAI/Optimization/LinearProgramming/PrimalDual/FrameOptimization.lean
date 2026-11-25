import OAI.Optimization.LinearProgramming.PrimalDual.FrameOptimizationCompose
import OAI.Optimization.LinearProgramming.PrimalDual.Ending

/-! The concrete Corollary 1.2 optimizer calls the chosen feasibility program at most twice. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

/-- The fixed uniform first call, joint feasibility call, three actual exits, and their
costs give strong polynomiality with the original optimization input encoding. -/
theorem stronglyPolynomialOptimization_of_feasibility
    (feasibility : StronglyPolynomialFeasibility) : StronglyPolynomialOptimization :=
  optimization_of_verified_return_paths Bridge.firstReturn Bridge.endingCode
    ⟨Bridge.afterFirst_certificate, Bridge.afterFirst_feasible⟩ feasibility

end PrimalDual
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.Geometry.MarkedCore
import OAI.Optimization.LinearProgramming.Geometry.LabelControl

/-! The post-prefix continuation cannot issue a new scalar query. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM OracleSegments

/-- Each instruction after completion or interruption of the pivot prefix is ordinary. -/
theorem LabelControl.continuation_coreOnly (after : Block) : CoreOnly (LabelControl.continuation after) :=
  CoreOnly.seq (CoreOnly.core _) (CoreOnly.branch _ (CoreOnly.core _) (CoreOnly.core _))

end Geometry
end LinearProgramming
end Optimization
end OAI

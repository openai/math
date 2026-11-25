import OAI.Optimization.LinearProgramming.Geometry.PostGram
import OAI.Optimization.LinearProgramming.Geometry.PostPivotLayout
import OAI.Optimization.LinearProgramming.Geometry.UniformGramCore

/-! The fixed Gram, residual, and Frank–Wolfe instruction block shared by the
rational scalar-size proof and the ordered-field caller. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM

def afterPrefixBlock : Block :=
  .seq PostPivotLayout.prepare (.seq uniformGramBlock postGramLabel)

def afterPrefixTime (r n : ℕ) : ℕ := 64*(r+n+1)^2 + uniformGramTime r n + postGramTime r n

end Geometry
end LinearProgramming
end Optimization
end OAI

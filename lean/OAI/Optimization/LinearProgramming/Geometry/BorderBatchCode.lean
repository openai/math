import OAI.Optimization.LinearProgramming.Geometry.BorderCandidate
import OAI.Optimization.LinearProgramming.Geometry.BorderBatchCore

/-! Shared geometric candidate loop and complete determinant/scan ROM, together
with their dimension-only instruction budgets. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM Contract OracleSegments

def scan : Segment := (Segment.core BorderScatter.init).seq (.loop (.addrLT 90 130) candidate)

def scanCost (k n : ℕ) : ℕ := n*(candidateCost k n+2)+6

/-- Every emitted instruction is dimension-independent, including the descriptor
constructor, determinant service, encoded oracle calls, restart handling and packing. -/
def batchProgram : Segment := .seq (.core prepare) scan

def batchTime (r n : ℕ) : ℕ := 41*(r+n+1)^2+(n*(2200*(n+1)^7+17)+2)+scanCost r n

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI

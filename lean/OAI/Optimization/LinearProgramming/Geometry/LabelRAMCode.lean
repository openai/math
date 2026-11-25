import OAI.Optimization.LinearProgramming.Geometry.AfterPrefixCode
import OAI.Optimization.LinearProgramming.Geometry.LabelControl
import OAI.Optimization.LinearProgramming.Geometry.PivotPrefixContract
import OAI.Optimization.LinearProgramming.OracleSpec.Compression

/-! Shared geometric label ROM, public register frame, and dimension-only time budget. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace LabelRAM

open RAM Contract OracleSegments

/-- This subroutine is a fixed segment once its fixed candidate-batch segment is linked. -/
def segment (batch : Segment) : Segment :=
  .seq (PivotPrefixRAM.program batch) (LabelControl.continuation afterPrefixBlock)

def program (batch : Segment) : OracleProgram := LabelControl.taggedProgram (segment batch)

structure Preserved {K : Type} (r n free : ℕ) (pre final : Memory K) : Prop where
  data (a) : 64≤a → (a<free ∨ free+2*n*r+5*r^2+2*n^2+2*n≤a) → final.data a=pre.data a
  index (a) : 72≤a → final.index a=pre.index a

/-- Permanent geometry arguments, including the designated index and the dual source,
survive the call. The three variable prefix cursors have separate output semantics. -/
def HeaderPreserved {K : Type} (base t : Memory K) : Prop :=
  ∀ a, 129≤a → a≤149 → a≠135 → a≠137 → a≠139 → t.index a=base.index a

def time (r n C : ℕ) : ℕ := r*PivotPrefixRAM.stepCost n (OracleSpec.MinorLog.threshold n) C + afterPrefixTime r n + 12

end LabelRAM
end Geometry
end LinearProgramming
end Optimization
end OAI

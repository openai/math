import OAI.Optimization.LinearProgramming.Geometry.LabelRAMCode
import OAI.Optimization.LinearProgramming.Geometry.BorderBatchCode

/-! The dimension-independent finite program shared by rational and real label calls. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open OracleSegments

/-- A fixed instruction list for the scalar-oracle calling convention. -/
def geometricLabelProcedure : Segment := LabelRAM.segment BorderBatch.batchProgram

end Geometry
end LinearProgramming
end Optimization
end OAI

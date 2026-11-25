import OAI.Optimization.LinearProgramming.Compression.ServiceTableAddress
import OAI.Optimization.LinearProgramming.Compression.ServiceTableScan
import OAI.Optimization.LinearProgramming.Compression.ServiceStageSlotBlock

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

/-- Interpret every scalar table row and leave the rank and membership bit in registers. -/
def lookup (cmp : Block) : Block := .seq prepareTable (.seq stageSlot (scanLoop cmp))

def lookupCost (C : ℕ→ℕ) (n g : ℕ) := prepareCost n g+40*(n+1)^2+(g*(C n+4*stride n+12)+1)

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI

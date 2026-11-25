import OAI.Optimization.LinearProgramming.PrimalDual.ArrayRAM
import OAI.Optimization.LinearProgramming.Recovery.InitialPairCopy

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PrimalOutput
open RAM Geometry PrimalDual

private def diffBlock : Block:=OutputPass.scanFromRegs .difference 220 221 222 28
def assemble : Block:=.seq diffBlock InitialPair.copyBlock

def assembleTime (m d : ℕ) := (10*m+6)+uniformTableTime d m (InitialPair.readBound d m)

end PrimalOutput
end Recovery
end LinearProgramming
end Optimization
end OAI

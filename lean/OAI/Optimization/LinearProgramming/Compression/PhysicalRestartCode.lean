import OAI.Optimization.LinearProgramming.Compression.BinaryRestoreFrame
import OAI.Optimization.LinearProgramming.Compression.ServiceTableInsert

/-! The common return-frame restoration and generator insertion bytecode. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM GeneratorTable

def restartPointers : List AddressSet := [.read 14 93,.read 18 95,.read 19 45,.read 20 97,.read 21 99]

/-- The incoming rank in physical address 3 is saved before that register becomes the
restore-loop cursor. All other descriptors survive the restore and are copied back into
the native generator-table ABI. -/
def physicalRestartPost : Block := .seq (.op (.addrCopy 45 3)) (.seq restoreScalarFrameBlock
  (.seq (addressPlan restartPointers) insertAtRank))

def restartPostBound (n g live : ℕ) : ℕ := 7*(live-1)+9+30*(g+1)*(stride n+1)

end Compression
end LinearProgramming
end Optimization
end OAI

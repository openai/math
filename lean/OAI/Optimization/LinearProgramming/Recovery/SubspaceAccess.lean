import OAI.Optimization.LinearProgramming.Recovery.SubspaceKernel
import OAI.Optimization.LinearProgramming.RAM.CallableScopedAccess

/-! The public finite-window proof uses only fixed data-address operands here.
The price kernel is an invoked finite ROM, with the same operands at every call site. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG
open RAM RAM.Callable OracleSpec

instance subspaceKernel_fixedAccess (p : BitProgram) (B : Polynomial ℕ) (minor : Program) :
    Fragment.FixedAccess (subspaceKernel p B minor) := by
  unfold subspaceKernel retry episode resetEpoch exposeWord epochLoop framedLoop boundary transfer priceHandler
    Geometry.VMPacketCopy.fragment numericCall Odd.leaf
  infer_instance

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI

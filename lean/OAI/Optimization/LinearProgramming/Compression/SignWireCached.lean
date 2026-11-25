import OAI.Optimization.LinearProgramming.Compression.CachedSign
import OAI.Optimization.LinearProgramming.Compression.SignWireInvoke
import OAI.Optimization.LinearProgramming.Compression.SignWireProtocol
import OAI.Optimization.LinearProgramming.Compression.SignWireAddressEnvelope

/-! Inside the BitRAM sign handler, the entire fixed arithmetic comparator
runs as one native subroutine. The live VM heap occupies the other bank. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire
open RAM RAM.Callable MinorProxyCache
open scoped BigOperators

@[simp] theorem comparisonTag_formOrdering (x : ℝ) :
    comparisonTag (formOrdering x) = if x<0 then 0 else if 0<x then 2 else 1 := by
  unfold formOrdering;split_ifs <;> rfl

/-- Only the even native bank sees the conditional halt table. Physical
address 14 receives its literal three-way return; the public heap stays odd. -/
def isolatedCachedCompare : Fragment := isolatedSign (cachedProxySignFragment (.index 14))

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI

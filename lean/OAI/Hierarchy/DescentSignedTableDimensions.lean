import OAI.Hierarchy.DescentSharedCableSerial
import OAI.Hierarchy.DescentHaloWalkRAM

namespace OAI
/-! Shared scalar widths of the actual packed formats and numerical ROM. -/
namespace Hierarchy
open DescentSharedCableNames DescentHaloWalkRAM DescentSIMDLookup
namespace DescentParallelBase.PackedBase
def width (D K L : ℕ) := Packed.bits D+(1+(Packed.bits K+Packed.bits L))
end DescentParallelBase.PackedBase
namespace DescentParallelBase.ParentFilter.Fused.TablesROM
def unit (D Q K L b : ℕ) :=
  let p:=breadth D
  let wd:=DescentParallelBase.PackedBase.width (p*p*Q) K L
  max (b*11+b) (wd+wd)
end DescentParallelBase.ParentFilter.Fused.TablesROM
namespace DescentPackedChildNeighbor.SIMD.ROM
def cells (T a b M H G : ℕ) := 2^(a*M)+(T*2^(a*M+b)+(2^(b*M)+(2^((b+b)*M)+H*chunks G M)))
end DescentPackedChildNeighbor.SIMD.ROM
end Hierarchy

end OAI

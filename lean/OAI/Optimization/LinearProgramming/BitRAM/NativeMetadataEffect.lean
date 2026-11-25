import OAI.Optimization.LinearProgramming.BitRAM.Ops
import OAI.Optimization.LinearProgramming.BitRAM.PacketLayout

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM

variable {K : Type*}

open RAM OracleSpec

/-- A native encoder writes only its declared packet and scratch scalars. The encoded
output length goes in 49, while the application's ports and high even numerical cache survive. -/
structure MetadataEffect [Zero K] [One K] (m t : Memory K) (w : Word) : Prop where
  packet : ScalarPacket t (m.index recvBaseReg) w
  length : t.index recvLenReg=w.length
  headers : ∀ i, 43 ≤ i → i<65 → i≠recvLenReg → t.index i=m.index i
  even : StableEven m t
  data : ∀ i, 3 ≤ i → i<m.index recvBaseReg ∨ m.index recvBaseReg+w.length ≤ i → t.data i=m.data i

end BitRAM
end LinearProgramming
end Optimization
end OAI

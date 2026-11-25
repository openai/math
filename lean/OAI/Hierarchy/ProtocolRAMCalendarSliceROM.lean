import OAI.Hierarchy.ProtocolRAMFeed
import OAI.Hierarchy.ProtocolRAMBinarySpan

namespace OAI
/-! # Finite public address extent for the deterministic reserve-slice table -/

namespace Hierarchy.ProtocolRAM.Calendar

/-- The advised slice ROM is placed after the complete initial stock. Its
physical row contains exactly the integer floor difference for that step and reserve. -/
def sliceROM (start steps stride : ℕ) : Bank :=
  ⟨start,ProtocolRAMPurchaseSampler.bits (steps*stride)⟩

theorem sliceROM_size (start steps stride : ℕ) : steps*stride≤(sliceROM start steps stride).size :=
  (ProtocolRAMPurchaseSampler.lt_span _).le

theorem sliceROM_size_le (start steps stride : ℕ) :
    (sliceROM start steps stride).size≤2*(steps*stride+1) :=
  ProtocolRAMPurchaseSampler.span_le _

end Hierarchy.ProtocolRAM.Calendar

end OAI

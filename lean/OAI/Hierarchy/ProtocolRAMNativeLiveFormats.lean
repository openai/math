import OAI.Hierarchy.ProtocolRAMNativeFormat
import OAI.Hierarchy.ProtocolRAMCalendarPrevious

namespace OAI
/-! # The stock address preceding each chronological repair -/

namespace Hierarchy.ProtocolRAM.Calendar
noncomputable section
variable {z d k q goods : ℕ}

def publishedStock (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods) : Event→ℕ
  | .attempt a => (format a).pricedArea.output
  | .feed b => arena.base c (.feed b)

section
variable (c : Mesh) (arena : Arena) (initial : ℕ)
  (build : Attempt→ℕ→Format z d k q goods)

/-- A preliminary compilation supplies only ordinal addresses and scan lengths.
No price lookup, stock operand, or sparse-write expression is reused from it. -/
def resolvedStock (a : Attempt) : ℕ :=
  previousStock c initial (publishedStock c arena (fun u=>build u initial)) (.attempt a)

/-- Emit the genuine stock-dependent failure, price, capacity and wire computations
from the resolved incoming address. Install the final native failed-ball mask and
the actual choice header within the strip builder before compiling the signed updates. -/
def liveFormats (a : Attempt) : Format z d k q goods :=
  build a (resolvedStock c arena initial build a)

end
end
end Hierarchy.ProtocolRAM.Calendar

end OAI

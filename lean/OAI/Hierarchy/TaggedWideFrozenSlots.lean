import OAI.Hierarchy.ProtocolRAMFrozenFormat

namespace OAI
/-! # The rectangular aperture of a frozen native format -/

namespace Hierarchy.ProtocolRAMFrozenWindow
/-- The static rectangular payload aperture used for both the live installed
board and the native scatter. -/
def Format.withSlots (s : Format) (ports lanes : ℕ) : Format := {s with D:=ports*lanes}

end Hierarchy.ProtocolRAMFrozenWindow

end OAI

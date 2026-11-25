import OAI.Hierarchy.ProtocolRAMOccurrenceHeader
import OAI.Hierarchy.ProtocolRAMSchedule

namespace OAI
/-! # Lookup bounds of the four physical repair occurrence columns -/
namespace Hierarchy.ProtocolRAM.Calendar
open StockCommit
variable {cut : ℕ}

/-- The four physical lookup tables share the bounded interval ending at stop. -/
theorem StockCommit.PortHeader.input_ends (h : PortHeader) (room : h.stop≤cut) :
    h.ballTerm.inputEnd≤cut ∧ h.fieldTerm.inputEnd≤cut ∧
      h.owner.base+h.owner.size≤cut ∧ h.parity.base+h.parity.size≤cut := by
  change h.start+2*h.small+h.large+h.large≤cut at room
  change max (h.start+h.small) 0≤cut ∧ max (h.start+h.small+h.small) 0≤cut ∧
    h.start+2*h.small+h.large≤cut ∧ h.start+2*h.small+h.large+h.large≤cut
  omega

end Hierarchy.ProtocolRAM.Calendar

end OAI

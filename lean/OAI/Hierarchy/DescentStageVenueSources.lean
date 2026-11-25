import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! The physical source banks used to publish a successor venue. -/
namespace Hierarchy.DescentSixParty.StageVenueTail
open ProtocolRAM

structure Sources where
  roster : Bank
  hub : Bank
  alive : ℕ→Bank
  paid : ℕ→Bank
  signed : ℕ→ℕ→Bank

end Hierarchy.DescentSixParty.StageVenueTail

end OAI

import OAI.ThreeFlat.Diagonal.TickScratchRegion

namespace OAI
namespace ThreeFlat.RAM.TickTerminalRoot
open Diagonal.TickWorkspace

/-- The selected body only changes its S12/S13 node slices and the S14–18 scratch. -/
def slotKeep (u addr : ℕ) : Prop := addr<base u 12 ∨ base u 19≤addr

end ThreeFlat.RAM.TickTerminalRoot

end OAI

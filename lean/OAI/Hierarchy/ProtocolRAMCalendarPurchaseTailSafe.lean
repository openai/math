import OAI.Hierarchy.ProtocolRAMCalendarArena
import OAI.Hierarchy.ProtocolRAMCalendarTailPositions
import OAI.Hierarchy.ProtocolRAMCalendarVerdict

namespace OAI
/-! Protection of a stored purchase word at every later position in its reserve history. -/
namespace Hierarchy.ProtocolRAM.Calendar
variable {w q goods : ℕ}
/-- The immutable key and reserve words of a prospective purchase precede every
write of its entire reserve timeline, including the last feed with no remaining trial. -/
theorem purchaseTail_safe (C : Chart w q goods) (arena : Arena) (p a j b x : ℕ)
    (floor : ∀ e u,u<arena.base C.mesh e→protected C u e)
    (slab : x<arena.base C.mesh (.attempt (.outer p a))+arena.stride) :
    ∀ e∈purchaseTail C.mesh p a j b,protected C x e := by
  intro e he
  apply floor
  exact slab.trans_le (arena.apart C.mesh (purchaseTail_after C.mesh p a j b e he))

end Hierarchy.ProtocolRAM.Calendar

end OAI

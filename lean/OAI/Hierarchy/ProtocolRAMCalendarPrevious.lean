import OAI.Hierarchy.ProtocolRAMCalendarArena

namespace OAI
/-! # The previous stock address on the chronological event schedule -/
namespace Hierarchy.ProtocolRAM.Calendar
open scoped Classical
noncomputable section

/-- Indexing the actual fixed chronological schedule by its ordinal recovers
that ordinal. This covers zero inner or outer fuel without a fictitious predecessor. -/
theorem position_at (c : Mesh) {u : ℕ} (hu : u<(events c).length) :
    position c (events c)[u]=u := by
  have view := congrArg (fun xs : List ℕ=>xs[u]?) (positions c)
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hu,Option.map_some,List.getElem?_range hu,
    Option.some.injEq] using view

/-- All purchase shelves and feed sources read the previous event's published
active inventory. At the first event, they read the initial stock bank. -/
def previousStock (c : Mesh) (initial : ℕ) (published : Event → ℕ) (e : Event) : ℕ :=
  let j := position c e
  if h : 0<j ∧ j≤(events c).length then published ((events c)[j-1]'(by omega)) else initial

end
end Hierarchy.ProtocolRAM.Calendar

end OAI

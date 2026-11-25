import OAI.Hierarchy.DescentDatedAnchorFieldRoomCore
import OAI.Hierarchy.DescentDatedPhysicalMatcherIndex

namespace OAI
/-! # Bounds on the two fields at the physical ordinary matcher index -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentRawCablePanel DescentSIMDLookup DescentDatedOperandPages DescentHaloWalkRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I)
local notation "fmt" => v.ticket.depotShape v.short

/-- Every original matcher/sibling source at this index has a bounded old ordinal and role,
including a missing sibling, a missing pair, and a word truncated at the packed output width. -/
theorem match_anchor_field_room (profile b : ℕ)
    (i : Fin (breadth (fmt).degree*((fmt).blocks*((fmt).cap*3)))) (source : Cell (DepotRAM.totalBits fmt)) :
    (law fmt profile b (v.matchAnchorIndex i 1).2.val source).val≤2*(fmt).cap ∧
      (law fmt profile b (v.matchAnchorIndex i 2).2.val source).val<11 :=
  matcher_index_room fmt _ profile b i source

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

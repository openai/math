import OAI.ThreeFlat.Routing.PackedRows

namespace OAI
/-! # Indexed ports of a fixed-width block of records -/

noncomputable section
namespace Hierarchy.Tagged
open ThreeFlat.Routing.SortNetwork
namespace SortRelation
abbrev Data (h w : ℕ) := Fin (Fintype.card (Payload h w))
end SortRelation
namespace SortedBlock
variable {l w : ℕ}
def unwrap (x : SortRelation.Data l w → Bool) : Records l w :=
  fun i j => x (Fintype.equivFin _ (i,j))

@[simp] theorem pack_unwrap (x : SortRelation.Data l w → Bool) : pack (unwrap x) = x := by
  funext i
  simp [pack,unwrap,Function.uncurry]
@[simp] theorem unwrap_pack (x : Records l w) : unwrap (pack x) = x := by
  funext i j
  simp [pack,unwrap,Function.uncurry]

end SortedBlock
end Hierarchy.Tagged
end

end OAI

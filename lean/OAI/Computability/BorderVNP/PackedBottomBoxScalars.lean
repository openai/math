import OAI.Computability.BorderVNP.PackedBottomBoxLocality
import OAI.Computability.BorderVNP.PackedBankInheritedScalarBounds

/-! # Frozen public scalar fields at the original repeated grid

The public reference carries its real stride even for zero copies. Each
equality carries the full original word width even when its repeated word is
empty. Inclusive ends, together with the copy capacity, bound these fields.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomRepeat

open Crossing Inherited CellSparse
open scoped Classical
open private rowEnd wideEnd from OAI.Computability.BorderVNP.PackedBottomBoxLocality

variable {D qe qa : ℕ} {A : Type} [Fintype A] {width : A → ℕ}
variable (N : Network D A width) (edges : N.Edge ↪ Fin qe) (ports : A ↪ Fin qa) (v : N.Site)
variable (copies capFine stride : ℕ) (box : List Factor)
local notation "s₀" => bornWith N edges ports v copies capFine stride box

/-- Every native frozen integer is controlled by the total bank size, the
one-copy stride, the number of copies and the fixed box opcode tag. -/
theorem bornWith_scalarBound (fits : capFine+incoming N v ≤ stride) :
    (s₀).ScalarBound (max 2 (max copies (max stride (s₀).size))) := by
  intro a ha
  obtain ⟨r,hr,ha⟩ := List.mem_flatMap.mp ha
  simp only [Site.rows,bornWith,List.reverse_singleton,List.flatten_cons,List.flatten_nil,List.append_nil,
    List.singleton_append,List.mem_cons] at hr
  change a.2 ≤ max 2 (max copies (max stride (copies*stride+incoming (wide N copies) v)))
  rcases hr with rfl | hr
  · change a ∈ [(.plain,2),(.boxID,0),(.bitAddress,0),(.plain,copies),(.plain,stride)] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> omega
  · obtain ⟨z,_,rfl⟩ := List.mem_map.mp hr
    have he := rowEnd N edges ports v z
    have hw := wideEnd N edges ports v copies z
    change a ∈ [(.plain,1),(.plain,copies),(.plain,rowWidth N v z),
      (.bitAddress,capFine+oneStart N edges ports v z),(.plain,stride),(.plain,1),
      (.bitAddress,copies*stride+wideStart N edges ports v copies z),(.plain,rowWidth N v z),(.plain,1)] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> omega

end Packing.BottomRepeat

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.PackedFrozenNodeProgram

/-! # Changing the enumeration used by the physical frozen writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Node

open Crossing Shortening Shortening.SeedIntervals StaticRows DirectoryCircuit CellAddressCircuit VPVNP.VerifierNetwork
open scoped Classical

variable {D m n s old np C C' d d' k k' w : ℕ} [NeZero D] {K : Type*} [Field K]
    {e : PaidIdentity K D m} {first : Fin D × Bool} {hm : 0 < m}
    {A : Type} {left right : Fintype A} {seed : A ↪ Fin n}
    {σ R B : Type*} [Fintype σ] [Fintype R] [Fintype B] {S : Schema R B}
    {carried : Frame σ (Pins R B d')} {oldF : Fields s old np C d k w σ}
    {newF : Fields (siteCapacity e s n) (edgeCapacity e old n) np C' d' k' w σ}
    {cut : Frame σ ((Fin old × Band D) × CutCircuit.Result × Fin w)}
    {work extent : Fin s → Fin w → σ} {before : Fin old → σ} {used : Fin np → Bool}
    {after : Fin (edgeCapacity e old n) → σ} {x : σ → Bool} {V : Type*} {key : V ↪ ℕ} {states : V → Site}

/-- A count frame at the specified seed enumeration. Its wires keep their original names. -/
abbrev CountFrame {A σ : Type*} [Fintype σ] (f : Fintype A) (j w : ℕ) : Type _ := by
  letI := f
  exact Frame σ (A × Option (Fin j) × Fin w)

/-- The numerical rows and chronological order of the native node agree
when the same count gates are viewed with either seed enumeration. -/
theorem image_enumeration {l : CountFrame (σ := σ) left e.count w} {r : CountFrame (σ := σ) right e.count w}
    (counts : HEq l r)
    (image : letI := left
      (schema e first (A := A) S old np w).Image
        ((frame e first hm seed carried oldF newF cut l work extent before used after).eval x) key states) :
    letI := right
    (schema e first (A := A) S old np w).Image
      ((frame e first hm seed carried oldF newF cut r work extent before used after).eval x) key states := by
  have same : left = right := Subsingleton.elim _ _
  subst right
  cases counts
  exact image

end Packing.Inherited.FrozenTape.Node

end BorderVNP
end Computability
end OAI

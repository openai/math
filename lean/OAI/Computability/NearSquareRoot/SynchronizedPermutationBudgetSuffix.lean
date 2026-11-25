import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetMask

/-! # The packed spectator suffix of a Beneš mask -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Packed
open IntegerMultiplication.Code IntegerMultiplication.Loom IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims

private theorem append_suffix {p h g B : ℕ}
    (a : SpanKey (field 2 p) (field 2 g) (field 2 0) (Block 2 h)) (s : Block 2 B) :
    (tile 2 (p+h+g+h) B).cast ((flatSpan p h g 0).cast a,s) =
      (flatSpan p h g B).cast (a.1,a.2.1,a.2.2.1,a.2.2.2.1,s) := by
  have empty : most a.2.2.2.2 = [] := List.length_eq_zero_iff.mp (by simp)
  apply Adic.distinct
  rw [tile_most,flatSpan_most,flatSpan_most]
  simp only [empty,List.append_nil,List.append_assoc]

/-- Appending the same low word before or after the physical XOR yields
the same full address, including leading zeros in the low word. -/
theorem flatMask_suffix {p i H g B : ℕ} (ctrl : Block 2 p → Fin i → Bool)
    (word : Block 2 (p+cap i H 0+g+cap i H 0)) (s : Block 2 B) :
    flatMask (H := H) p g B ctrl ((tile 2 _ B).cast (word,s)) =
      (tile 2 _ B).cast (flatMask (H := H) p g 0 ctrl word,s) := by
  obtain ⟨a,rfl⟩ := (flatSpan p (cap i H 0) g 0).cast.surjective word
  rw [append_suffix]
  simp only [flatMask,Equiv.symm_apply_apply]
  exact (append_suffix (p := p) (g := g) (h := cap i H 0) (a.1,maskBlock (ctrl a.1) a.2.1,a.2.2) s).symm

end Controlled

end NearSquareRoot
end Computability
end OAI

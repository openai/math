import OAI.LinearAlgebra.SpectralBooks.Manuscript
import OAI.LinearAlgebra.SpectralBooks.WireMetricBaseChange
import OAI.LinearAlgebra.SpectralBooks.TreeGridCompression
import OAI.LinearAlgebra.SpectralBooks.TreeIndependentSetHardness

/-! # The matrix theorems from the companion border-stretch lemma

In the tree case, the two-dimensional crossing can be shortened. Border
stretch makes one family of subcubic bipartite independent-set grids hard,
while planar compression gives small exact programs for those same grids.
The contradiction yields a finite non-tree witness in the reference field.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

/-- Dimension two of border stretch suffices to exclude the tree phase. -/
theorem hasNonTreeWireMetric_of_borderStretch (K : Type) [Field K] [Infinite K]
    (stretch : Crossing.HasProfileShortening K 2 → ∃ ε : ℝ, 0 < ε ∧ SignedWitnessHardness K ε) :
    HasNonTreeWireMetric K := by
  by_contra tree
  obtain ⟨δ,hδ,hard⟩ := hardSubcubicGrids_of_shortening_stretch tree stretch
  exact tree (hasNonTreeWireMetric_of_hardSubcubicGrids hδ hard)

/-- The plane and all three finite rank bounds in every field of the characteristic
follow from the two-dimensional border stretch in a single infinite reference field. -/
theorem matrix_theorems_of_borderStretch (K : Type) [Field K] [Infinite K]
    (stretch : Crossing.HasProfileShortening K 2 → ∃ ε : ℝ, 0 < ε ∧ SignedWitnessHardness K ε)
    (F : Type*) [Field F] (hchar : ringChar K = ringChar F) :
    HasNonTreeWireMetric F ∧ RectangularRankBound F ∧ 3 / Real.sqrt 2 ≤ formalOmega F 1 1 1 ∧
      3 / Real.sqrt 2 ≤ divisionOmega F 1 1 1 := by
  have h := hasNonTreeWireMetric_of_borderStretch K stretch
  exact ⟨(hasNonTreeWireMetric_iff_of_ringChar_eq hchar).mp h,
    rank_and_exponent_of_nonTreeWireMetric h F hchar⟩

/-- A small algebraically closed reference field exists for every characteristic. -/
theorem exists_algebraicallyClosed_reference {p : ℕ} (hp : p.Prime ∨ p = 0) :
    ∃ (K : Type) (_ : Field K), IsAlgClosed K ∧ CharP K p := by
  rcases hp with hp | rfl
  · let : Fact p.Prime := ⟨hp⟩
    exact ⟨AlgebraicClosure (ZMod p), inferInstance, inferInstance, inferInstance⟩
  · exact ⟨AlgebraicClosure ℚ, inferInstance, inferInstance, inferInstance⟩

end SpectralBooks
end LinearAlgebra
end OAI

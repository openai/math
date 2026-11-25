import OAI.Combinatorics.Sunflower.FilterBound
import OAI.Combinatorics.Sunflower.Correction

/-! # Alphabet-uniform filtering at a positive diagonal gap -/

open scoped Classical
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower

/-- A positive partial-diagonal gap admits equality tests at a common bounded
price for all finite alphabets. Each local matrix uses only its own control. -/
theorem exists_equality_filter {I : Type} [Fintype I] [Nonempty I] [dec : DecidableEq I]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    (P T : Finset I) (hP : P.Nonempty) (hT : T.Nonempty) (hPT : Disjoint P T)
    (hg : 0 < maskDiagonalPrice φ 1 P + maskDiagonalPrice φ 1 T - maskDiagonalPrice φ 1 (P ∪ T)) :
    ∃ C : ℝ, ∀ n : ℕ, ∃ R Q : Raw.{0} I ℂ, R.coeff ≠ 0 ∧ Q.coeff ≠ 0 ∧
      rawLogPrice φ 1 R - rawLogPrice φ 1 Q ≤ C ∧ EqualityMaps P T (Fin n) R Q := by
  have hdec := Subsingleton.elim dec (Classical.decEq I)
  subst dec
  let g := maskDiagonalPrice φ 1 P + maskDiagonalPrice φ 1 T - maskDiagonalPrice φ 1 (P ∪ T)
  have hpos : 0 < g := hg
  obtain ⟨h, hh, he⟩ := exists_broadcastParameter (θ := 1) hpos
  rw [mul_one] at he
  apply exists_equality_filter_of_corrections φ P T
    (hP.mono Finset.subset_union_left) (half_pos hpos)
    (B := 2 * broadcastOverhead (Fintype.card I) h)
  intro b
  obtain ⟨U,V,hU,hV,hcor,hcost⟩ := exists_correction φ P T hP hT hPT (by omega : 0 < h) b
  refine ⟨U,V,hU,hV,hcost.trans ?_,hcor⟩
  push_cast
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  dsimp [g] at he ⊢
  linarith only [he]

end Sunflower
end Combinatorics
end OAI

import OAI.LinearAlgebra.SpectralBooks.SiteFlatteningOperations
import OAI.LinearAlgebra.SpectralBooks.SiteFlatteningProduct
import OAI.LinearAlgebra.SpectralBooks.TensorSemiring
import OAI.LinearAlgebra.SpectralBooks.Spectrum

/-! # Spectral points from proper bipartitions of the sites

The flattening rank depends only on the mutual-restriction class. Each proper
bipartition gives a normalized spectral point over any field.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped NNReal Classical

noncomputable section

namespace SiteTensor

universe v u w

open Crossing

variable {I : Type u} (s : I → Prop) [DecidablePred s] [Fintype I] (K : Type w) [Field K]

/-- The matrix rank across the cut of a tensor class. -/
def cutRank : TensorClass.{v} I K → ℕ :=
  Quotient.lift (fun X : Raw.{v} I K => (cutMatrix s X.coeff).rank) fun X Y h =>
    le_antisymm (cutMatrix_rank_le_of_restriction s X.coeff Y.coeff h.1)
      (cutMatrix_rank_le_of_restriction s Y.coeff X.coeff h.2)

@[simp] theorem cutRank_ofRaw (X : Raw.{v} I K) :
    cutRank s K (ofRaw X) = (cutMatrix s X.coeff).rank := rfl

/-- Across every cut restriction induces a matrix rank comparison. -/
theorem monotone_cutRank : Monotone (cutRank.{v} s K) := by
  intro x y
  refine Quotient.inductionOn₂ x y fun X Y h => ?_
  exact cutMatrix_rank_le_of_restriction s X.coeff Y.coeff h

variable [Nonempty I] [Nonempty {i // s i}] [Nonempty {i // ¬ s i}]

/-- The normalized spectral point associated to a proper cut. -/
def cutSpectrum : normalizedSpectrum (fun x y : TensorClass.{v} I K => x ≤ y) := by
  refine ⟨fun x => (cutRank s K x : ℝ≥0), ?_, ?_, ?_, ?_, ?_⟩
  · change ((cutMatrix s (Raw.zero.{v} I K).coeff).rank : ℝ≥0) = 0
    rw [Raw.cutMatrix_rank_zero, Nat.cast_zero]
  · change ((cutMatrix s (Raw.one.{v} I K).coeff).rank : ℝ≥0) = 1
    rw [Raw.cutMatrix_rank_one, Nat.cast_one]
  · intro x y
    refine Quotient.inductionOn₂ x y fun X Y => ?_
    change ((cutMatrix s (sumCoeff X.coeff Y.coeff)).rank : ℝ≥0) =
      ((cutMatrix s X.coeff).rank : ℝ≥0) + (cutMatrix s Y.coeff).rank
    exact_mod_cast cutMatrix_rank_sumCoeff s X.coeff Y.coeff
  · intro x y
    refine Quotient.inductionOn₂ x y fun X Y => ?_
    change ((cutMatrix s (X.mul Y).coeff).rank : ℝ≥0) =
      ((cutMatrix s X.coeff).rank : ℝ≥0) * (cutMatrix s Y.coeff).rank
    exact_mod_cast cutMatrix_rank_product s X.coeff Y.coeff
  · exact fun x y h => Nat.cast_le.mpr ((monotone_cutRank s K) h)

@[simp] theorem cutSpectrum_ofRaw (X : Raw.{v} I K) :
    (cutSpectrum s K).val (ofRaw X) = ((cutMatrix s X.coeff).rank : ℝ≥0) := rfl

/-- Every site set with at least two sites admits a normalized spectral point. -/
theorem spectrum_nonempty (I : Type u) [Fintype I] [Nontrivial I] (K : Type w) [Field K] :
    (normalizedSpectrum (fun x y : TensorClass.{v} I K => x ≤ y)).Nonempty := by
  classical
  obtain ⟨i, j, hij⟩ := exists_pair_ne I
  let s (x : I) := x = i
  let : Nonempty {x // s x} := ⟨⟨i, rfl⟩⟩
  let : Nonempty {x // ¬ s x} := ⟨⟨j, Ne.symm hij⟩⟩
  exact Set.nonempty_of_mem (cutSpectrum.{v} s K).property

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.SpectralBooks.Tensor
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Finite fields of definition for rank decompositions -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Foundation

section

/-- A rank decomposition of a finite tensor over an algebraic extension is
already defined over a finite-dimensional intermediate field. -/
theorem exists_finiteDimensional_rankAtMost {F K X Y Z : Type*}
    [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [Finite X] [Finite Y] [Finite Z] {T : Tensor F X Y Z} {r : ℕ}
    (h : Tensor.RankAtMost (fun x y z => algebraMap F K (T x y z)) r) :
    ∃ S : IntermediateField F K, FiniteDimensional F S ∧
      Tensor.RankAtMost (fun x y z => algebraMap F S (T x y z)) r := by
  rcases h with ⟨a, b, c, h⟩
  let coeff : Fin r × (X ⊕ Y ⊕ Z) → K :=
    fun p => p.2.elim (a p.1) (Sum.elim (b p.1) (c p.1))
  let S := IntermediateField.adjoin F (Set.range coeff)
  have hmem (i : Fin r) (j : X ⊕ Y ⊕ Z) : coeff (i, j) ∈ S :=
    IntermediateField.subset_adjoin F _ ⟨(i, j), rfl⟩
  refine ⟨S, IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := F) x).isIntegral), ?_⟩
  refine ⟨fun i x => ⟨a i x, hmem i (.inl x)⟩,
    fun i y => ⟨b i y, hmem i (.inr (.inl y))⟩,
    fun i z => ⟨c i z, hmem i (.inr (.inr z))⟩, ?_⟩
  funext x y z
  apply Subtype.ext
  simpa [Tensor.rankOne, IntermediateField.coe_sum] using congrFun (congrFun (congrFun h x) y) z

end

end SpectralBooks
end LinearAlgebra
end OAI

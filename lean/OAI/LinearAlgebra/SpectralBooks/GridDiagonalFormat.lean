import OAI.LinearAlgebra.SpectralBooks.BookDiagonalRaw
import OAI.LinearAlgebra.SpectralBooks.BookGroupSupport
import OAI.LinearAlgebra.SpectralBooks.DoublingSelection
import OAI.LinearAlgebra.SpectralBooks.GridLabelSets
import OAI.LinearAlgebra.SpectralBooks.WireSymmetry

/-! # The diagonal classes on the two grids used in doubling -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

section

open SiteTensor SiteTensor.BookFactors PermutationStretch

variable (F : Type*) [Field F]

private theorem grouped_support_of_range {A J : Type} [Fintype A] [Fintype J]
    (σ : A → J) (hσ : Function.Injective σ) (S : Finset J) (hS : ∀ j, j ∈ S ↔ ∃ a, j = σ a) :
    ofRaw ((Raw.diagonal S F (Fin 2)).group Subtype.val) =
      ofRaw ((Raw.diagonal A F (Fin 2)).group σ) := by
  let f (a : A) : S := ⟨σ a, (hS _).2 ⟨a, rfl⟩⟩
  let e := Equiv.ofBijective f ⟨fun _ _ h ↦ hσ (congrArg Subtype.val h), by
    intro ⟨j, hj⟩
    obtain ⟨a, rfl⟩ := (hS j).1 hj
    exact ⟨a, rfl⟩⟩
  exact ofRaw_eq_iff.mpr (Raw.grouped_diagonal_reindex F (Fin 2) e Subtype.val)

variable (ι : Type) [Fintype ι] (n : ℕ)

/-- The joint grid labels are precisely the book sites. Auxiliary sites have scalar slots. -/
theorem ofRaw_gridLabels_union_diagonal :
    ofRaw ((Raw.diagonal ↥(gridLabels ι n false ∪ gridLabels ι n true) F (Fin 2)).group Subtype.val) =
      classOfProduct (jointDiagonal F (NoncentralGrid ι n) (NoncentralGrid ι n) (coordinateCubeCorners ι 1)) := by
  apply (grouped_support_of_range F Sum.inl Sum.inl_injective _ (fun _ ↦ mem_gridLabels_union_iff)).trans
  apply (ofRaw_eq_iff.mpr (Raw.group_inl_equivalent _ _)).trans
  exact ofRaw_eq_iff.mpr ⟨Raw.withTrivial_restricts _ bookRaw_diagAll_equivalent.2,
    Raw.withTrivial_restricts _ bookRaw_diagAll_equivalent.1⟩

private def leftIndex {B C O : Type} : Unit ⊕ B → BookSite B C ⊕ O
  | .inl u => .inl (.inl u)
  | .inr b => .inl (.inr (.inl b))

private theorem leftIndex_injective {B C O : Type} : Function.Injective (@leftIndex B C O) := by
  rintro (u | b) (v | d) h <;> simp_all [leftIndex]

private theorem ofRaw_leftIndex_diagonal {B C O : Type} [Fintype B] [Fintype C] [Fintype O] :
    ofRaw ((Raw.diagonal (Unit ⊕ B) F (Fin 2)).group (@leftIndex B C O)) =
      classOfProduct ((privateDiagonal F B).left O C) := by
  let σ := @leftIndex B C O
  let T := (Raw.diagonal (Unit ⊕ B) F (Fin 2)).group σ
  let U := Raw.withTrivial O (bookRaw (placeB C (privateDiagonal F B).coeff))
  let e (i : BookSite B C ⊕ O) : T.Leg i ≃ U.Leg i := by
    rcases i with ((u | (b | c)) | o)
    · exact fiberAtEquiv σ (fun _ ↦ Fin 2) (.inl u) (fun _ h ↦ leftIndex_injective h)
    · exact fiberAtEquiv σ (fun _ ↦ Fin 2) (.inr b) (fun _ h ↦ leftIndex_injective h)
    · exact fiberEmptyEquiv σ (fun _ ↦ Fin 2) _ (by rintro (_ | _) <;> simp [σ, leftIndex])
    · exact fiberEmptyEquiv σ (fun _ ↦ Fin 2) _ (by rintro (_ | _) <;> simp [σ, leftIndex])
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  let z (i : Unit ⊕ B) : Fin 2 := x (σ i) ⟨i, rfl⟩
  change (Raw.diagonal (Unit ⊕ B) F (Fin 2)).coeff z = diagonalCoeff (z (.inl ())) (fun b ↦ z (.inr b))
  rw [Raw.diagonal_coeff_at (.inl ()), diagonalCoeff]
  have hiff : (∀ i, z i = z (.inl ())) ↔ ∀ b, z (.inr b) = z (.inl ()) := by
    constructor
    · exact fun h b ↦ h (.inr b)
    · rintro h (⟨⟩ | b)
      · rfl
      · exact h b
  by_cases h : ∀ b, z (.inr b) = z (.inl ())
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun ht ↦ h (hiff.mp ht)), ite_eq_right h]

/-- The left grid labels are the common center and the sites of the first private diagonal. -/
theorem ofRaw_gridLabels_false_diagonal :
    ofRaw ((Raw.diagonal (gridLabels ι n false) F (Fin 2)).group Subtype.val) =
      classOfProduct ((privateDiagonal F (NoncentralGrid ι n)).left (coordinateCubeCorners ι 1)
        (NoncentralGrid ι n)) := by
  apply (grouped_support_of_range F leftIndex leftIndex_injective _ ?_).trans (ofRaw_leftIndex_diagonal F)
  intro j
  rw [mem_gridLabels_false_iff]
  constructor
  · rintro (rfl | ⟨b, rfl⟩)
    · exact ⟨.inl (), rfl⟩
    · exact ⟨.inr b, rfl⟩
  · rintro ⟨(⟨⟩ | b), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨b, rfl⟩

end

end

end SpectralBooks
end LinearAlgebra
end OAI

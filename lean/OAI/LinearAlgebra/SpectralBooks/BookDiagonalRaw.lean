import OAI.LinearAlgebra.SpectralBooks.BookRaw
import OAI.LinearAlgebra.SpectralBooks.StretchProducts
import OAI.LinearAlgebra.SpectralBooks.DiagonalProduct
import OAI.LinearAlgebra.SpectralBooks.TensorSemiring

/-! # Identifying the common book diagonal with the full diagonal on its sites -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped Classical
open MatrixMultiplication.Foundation

section

open PermutationStretch SiteTensor

variable {K : Type*} [Field K]

/-- The center supplies a reference label for equality at every other site, so
the common book diagonal is equivalent to the standard full diagonal. -/
theorem bookRaw_diagAll_equivalent {B C W : Type} [Fintype B] [Fintype C] [Fintype W] :
    (bookRaw (diagAll (K := K) B C W)).Equivalent (Raw.diagonal (BookSite B C) K W) := by
  let e : ∀ i, bookLeg W (fun _ : B => W) (fun _ : C => W) i ≃ W
    | .inl _ => Equiv.refl _
    | .inr (.inl _) => Equiv.refl _
    | .inr (.inr _) => Equiv.refl _
  apply Raw.reindex_equivalent e
  intro (x : ∀ i, bookLeg W (fun _ : B => W) (fun _ : C => W) i)
  refine Eq.trans ?_ (Raw.diagonal_coeff_at (K := K) (Sum.inl () : BookSite B C)
    (fun i => e i (x i))).symm
  obtain ⟨⟨u, l, r⟩, rfl⟩ := bookCoordinates.symm.surjective x
  let a := bookCoordinates.symm (u, l, r)
  have h : (∀ i : BookSite B C, e i (a i) = e (.inl ()) (a (.inl ()))) ↔
      (∀ b, l b = u) ∧ (∀ c, r c = u) := by
    constructor
    · exact fun h => ⟨fun b => h (.inr (.inl b)), fun c => h (.inr (.inr c))⟩
    · rintro ⟨hb, hc⟩ (⟨⟩ | b | c)
      · rfl
      · exact hb b
      · exact hc c
  have hb : (bookRaw (diagAll (K := K) B C W)).coeff a =
      diagonalCoeff u l * diagonalCoeff u r := rfl
  dsimp only [a] at hb h
  rw [hb]
  simp only [h, diagonalCoeff, ite_and, ite_mul, one_mul, zero_mul]
  split_ifs <;> rfl

/-- The two descriptions therefore define the same tensor-semiring class. -/
theorem ofRaw_bookRaw_diagAll {B C W : Type} [Fintype B] [Fintype C] [Fintype W] :
    ofRaw (bookRaw (diagAll (K := K) B C W)) = ofRaw (Raw.diagonal (BookSite B C) K W) :=
  ofRaw_eq_iff.mpr bookRaw_diagAll_equivalent

end

end SpectralBooks
end LinearAlgebra
end OAI

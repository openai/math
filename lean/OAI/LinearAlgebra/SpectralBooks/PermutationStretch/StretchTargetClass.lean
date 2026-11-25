import OAI.LinearAlgebra.SpectralBooks.SitePriceEval.StretchPriceModel
import OAI.LinearAlgebra.SpectralBooks.PrivateProducts
import OAI.LinearAlgebra.SpectralBooks.BookDiagonalRaw
import OAI.LinearAlgebra.SpectralBooks.SubsetPriceOrdinary

/-! # The class of a stretch target

The finite coordinate expression for the permutation stretch represents the
product of the shared diagonal and both private factors in the tensor
semiring. Adjoining one-dimensional auxiliary sites preserves this product.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open MatrixMultiplication.Foundation
open scoped Classical
namespace PermutationStretch
open SiteTensor SitePriceEval

variable {K : Type*} [Field K] {B C : Type} [Fintype B] [Fintype C]
  {U V : Type} [Fintype U] [Fintype V] {X : B → Type} {Y : C → Type}
  [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

/-- The two private factors differ from their local product only by
one-dimensional slots on their opposite sides. -/
theorem ofRaw_joinedPrivate (P : U → (∀ b, X b) → K) (Q : V → (∀ c, Y c) → K) :
    ofRaw (bookRaw (joinedPrivate P Q)) =
      ofRaw (bookRaw (placeB C P)) * ofRaw (bookRaw (placeC B Q)) := by
  apply ofRaw_eq_iff.mpr
  let e : ∀ i, (bookRaw (joinedPrivate P Q)).Leg i ≃
      ((bookRaw (placeB C P)).mul (bookRaw (placeC B Q))).Leg i
    | .inl _ => Equiv.refl _
    | .inr (.inl b) => (Equiv.prodUnique (X b) Unit).symm
    | .inr (.inr c) => (Equiv.uniqueProd (Y c) Unit).symm
  exact Raw.reindex_equivalent e (fun _ => rfl)

/-- The one-copy shared target as an actual tensor semiring product. -/
theorem ofRaw_sharedTarget (R : Type) [Fintype R] (P : U → (∀ b, X b) → K)
    (Q : V → (∀ c, Y c) → K) :
    ofRaw (bookRaw (sharedTarget (R := R) P Q)) = ofRaw (bookRaw (diagAll (K := K) B C R)) *
      ofRaw (bookRaw (placeB C P)) * ofRaw (bookRaw (placeC B Q)) := by
  have he : sharedTarget (R := R) P Q = splitProduct (diagAll B C R) (joinedPrivate P Q) := by
    funext u x y
    simp only [sharedTarget, splitProduct, diagAll, joinedPrivate, mul_assoc]
  rw [he, bookRaw_splitProduct, ofRaw_mul, ofRaw_joinedPrivate, mul_assoc]

/-- Inserting trivial auxiliary sites identifies the target with a power of
the binary diagonal times the two private tensors. -/
theorem ofRaw_withTrivial_sharedTarget {O : Type} [Fintype O] (k : ℕ)
    (P : U → (∀ b, X b) → K) (Q : V → (∀ c, Y c) → K) :
    ofRaw (Raw.withTrivial O (bookRaw (sharedTarget (R := Fin (2^k)) P Q))) =
      ofRaw (Raw.withTrivial O (bookRaw (diagAll (K := K) B C (Fin 2)))) ^ k *
        ofRaw (Raw.withTrivial O (bookRaw (placeB C P))) *
        ofRaw (Raw.withTrivial O (bookRaw (placeC B Q))) := by
  have he : ofRaw (bookRaw (diagAll (K := K) B C (Fin (2^k)))) =
      ofRaw (bookRaw (diagAll (K := K) B C (Fin 2))) ^ k := by
    simp only [ofRaw_bookRaw_diagAll, ofRaw_diagonal_fin_eq_natCast, Nat.cast_pow, Nat.cast_ofNat]
  have h := congrArg (withTrivialHom O) (ofRaw_sharedTarget (Fin (2^k)) P Q)
  rwa [he, map_mul, map_mul, map_pow] at h

/-- The additive notation for nonzero products used in clearing private
denominators is represented by the shared coefficient tensor. -/
theorem bookProduct_sharedTarget {O : Type} [Fintype O] (k : ℕ)
    (P : BookFactors.PrivateData K B) (Q : BookFactors.PrivateData K C) :
    BookFactors.bookProduct O (sharedTarget (R := Fin (2^k)) P.coeff Q.coeff)
      (sharedTarget_ne_zero P.coeff_ne Q.coeff_ne) =
      k • BookFactors.jointDiagonal K B C O + P.left O C + Q.right O B := by
  apply Additive.ext <| Subtype.ext ?_
  exact ofRaw_withTrivial_sharedTarget k P.coeff Q.coeff

end PermutationStretch

end

end SpectralBooks
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.SpectralBooks.BookRaw
import OAI.LinearAlgebra.SpectralBooks.SiteSliceRestriction

/-!
# Collapsing two private sets in opposite directions

Each grouped placement is regarded as a private tensor on the original set of
sites, by inserting one-dimensional legs. The original tensor is a restriction
of the literal product of these two tensors.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open MatrixMultiplication.Foundation
open scoped Classical BigOperators

section

variable {K : Type*} [Field K] {B C U : Type} [Fintype B] [Fintype C] [Fintype U]
  {X : B → Type} {Y : C → Type} [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]

/-- Group all `C` indices at the common site and leave one coordinate there
for each original coordinate on `B`. -/
def groupRight (T : Tensor K U (∀ b, X b) (∀ c, Y c)) :
    Tensor K (U × (∀ c, Y c)) (∀ b, X b) (C → Unit) := fun p x _ => T p.1 x p.2

/-- Group all `B` indices at the common site and retain the `C` coordinates. -/
def groupLeft (T : Tensor K U (∀ b, X b) (∀ c, Y c)) :
    Tensor K (U × (∀ b, X b)) (B → Unit) (∀ c, Y c) := fun p _ y => T p.1 p.2 y

/-- Doubling, equation `doubling-slices`, at the level of restriction. The
tensor on the right is the sitewise product of the two collapsed placements. -/
theorem restricts_product_collapsed_placements (T : Tensor K U (∀ b, X b) (∀ c, Y c)) :
    (bookRaw T).Restricts ((bookRaw (groupRight T)).mul (bookRaw (groupLeft T))) := by
  let P : Tensor K ((U × (∀ c, Y c)) × (U × (∀ b, X b))) (∀ b, X b) (∀ c, Y c) :=
    fun p x y => T p.1.1 x p.1.2 * T p.2.1 p.2.2 y
  have h := (siteRestriction_iff_isRestriction T P).mp (siteRestriction_grouped_product T)
  apply SiteTensor.restrict_trans h
  let e : ∀ i, bookLeg ((U × (∀ c, Y c)) × (U × (∀ b, X b))) X Y i ≃
      bookLeg (U × (∀ c, Y c)) X (fun _ : C => Unit) i ×
        bookLeg (U × (∀ b, X b)) (fun _ : B => Unit) Y i
    | .inl _ => Equiv.refl _
    | .inr (.inl b) => (Equiv.prodUnique (X b) Unit).symm
    | .inr (.inr c) => (Equiv.uniqueProd (Y c) Unit).symm
  exact SiteTensor.restrict_of_equiv e (fun _ => rfl)

end

end

end SpectralBooks
end LinearAlgebra
end OAI

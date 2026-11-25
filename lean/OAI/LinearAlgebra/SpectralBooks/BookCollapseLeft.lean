import OAI.LinearAlgebra.SpectralBooks.BookFiber
import OAI.LinearAlgebra.SpectralBooks.GroupedProduct

/-! # Grouping the left private sites at the common site -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation
open scoped Classical

/-- Move every site of the left branch to the common site. -/
def collapseBookLeft {B C : Type} : BookSite B C → BookSite B C
  | .inl _ => .inl ()
  | .inr (.inl _) => .inl ()
  | .inr (.inr c) => .inr (.inr c)

variable {B C U : Type} {X : B → Type} {Y : C → Type}

private def leftCommonFiber :
    ((k : {k : BookSite B C // collapseBookLeft k = .inl ()}) → bookLeg U X Y k.val) ≃
      U × (∀ b, X b) where
  toFun f := (f ⟨.inl (), rfl⟩, fun b => f ⟨.inr (.inl b), rfl⟩)
  invFun p
    | ⟨.inl _, _⟩ => p.1
    | ⟨.inr (.inl b), _⟩ => p.2 b
    | ⟨.inr (.inr _), h⟩ => nomatch h
  left_inv f := by
    funext ⟨k, hk⟩
    rcases k with _ | b | c
    · rfl
    · rfl
    · cases hk
  right_inv _ := rfl

private def leftCollapseLeg (j : BookSite B C) :
    ((k : {k // collapseBookLeft k = j}) → bookLeg U X Y k.val) ≃
      bookLeg (U × (∀ b, X b)) (fun _ : B => Unit) Y j := by
  rcases j with _ | b | c
  · exact leftCommonFiber
  · apply fiberEmptyEquiv
    rintro (_ | _ | _) <;> simp [collapseBookLeft]
  · apply fiberAtEquiv collapseBookLeft _ (.inr (.inr c))
    rintro (_ | _ | _) <;> simp [collapseBookLeft]

/-- The literal grouped tensor and the array with a pair at the common site
are related in both directions by the local coordinate identifications. -/
theorem bookRaw_group_collapseLeft {K : Type*} [Field K] [Fintype B] [Fintype C] [Fintype U]
    [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)] (T : Tensor K U (∀ b, X b) (∀ c, Y c)) :
    ((bookRaw T).group collapseBookLeft).Equivalent (bookRaw (groupLeft T)) := by
  apply SiteTensor.Raw.reindex_equivalent (fun j => leftCollapseLeg (U := U) (X := X) (Y := Y) j)
  intro x
  rfl

end SpectralBooks
end LinearAlgebra
end OAI

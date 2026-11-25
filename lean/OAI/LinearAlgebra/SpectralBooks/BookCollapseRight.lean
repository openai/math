import OAI.LinearAlgebra.SpectralBooks.GroupedProduct
import OAI.LinearAlgebra.SpectralBooks.BookFiber

/-! # The placement grouping the right-hand family at the common site -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation SiteTensor
open scoped Classical

variable {B C : Type}

/-- Move every index of the right-hand family to the common site. -/
def collapseBookRight : BookSite B C → BookSite B C
  | .inl _ => .inl ()
  | .inr (.inl b) => .inr (.inl b)
  | .inr (.inr _) => .inl ()

/-- The coordinates grouped at the center are the old center coordinate
and one coordinate from every right-hand site. -/
private def centerRightEquiv {U : Type} (X : B → Type) (Y : C → Type) :
    ((i : {i : BookSite B C // collapseBookRight i = .inl ()}) → bookLeg U X Y i.val) ≃
      (U × (∀ c, Y c)) where
  toFun x := (x ⟨.inl (), rfl⟩, fun c => x ⟨.inr (.inr c), rfl⟩)
  invFun p
    | ⟨.inl _, _⟩ => p.1
    | ⟨.inr (.inr c), _⟩ => p.2 c
  left_inv _ := by
    funext ⟨i, hi⟩
    obtain _ | (b | c) := i
    · rfl
    · contradiction
    · rfl
  right_inv _ := rfl

/-- A grouped placement and the explicit private tensor obtained by moving
the right-hand coordinates are mutually restrictive. -/
theorem bookRaw_group_collapseRight {K : Type*} {U : Type} [CommSemiring K] [Fintype B] [Fintype C]
    {X : B → Type} {Y : C → Type} [Fintype U] [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]
    (T : Tensor K U (∀ b, X b) (∀ c, Y c)) :
    ((bookRaw T).group collapseBookRight).Equivalent (bookRaw (groupRight T)) := by
  let e : ∀ j, ((bookRaw T).group collapseBookRight).Leg j ≃ (bookRaw (groupRight T)).Leg j
    | .inl _ => centerRightEquiv X Y
    | .inr (.inl b) => fiberAtEquiv collapseBookRight (bookLeg U X Y) (.inr (.inl b)) (by
        rintro (u | (b' | c)) h
        · contradiction
        · simpa [collapseBookRight] using h
        · contradiction)
    | .inr (.inr c) => fiberEmptyEquiv collapseBookRight (bookLeg U X Y) (.inr (.inr c)) (by
        rintro (u | (b | c')) h <;> simp [collapseBookRight] at h)
  exact Raw.reindex_equivalent e (fun _ => rfl)

end SpectralBooks
end LinearAlgebra
end OAI

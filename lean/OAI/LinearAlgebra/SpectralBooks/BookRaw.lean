import OAI.LinearAlgebra.SpectralBooks.SiteRestrictionBridge
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Raw

/-! # Book-site coordinates as a finite tensor format -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation
open scoped Classical

universe u v

variable {K B C : Type*}
  {U : Type u} {X : B → Type u} {Y : C → Type u}
  {U' : Type u} {X' : B → Type u} {Y' : C → Type u}
  [Fintype U] [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]
  [Fintype U'] [∀ b, Fintype (X' b)] [∀ c, Fintype (Y' c)]

/-- The finite tensor on the entire book site set, with its format recorded. -/
def bookRaw (T : Tensor K U (∀ b, X b) (∀ c, Y c)) : SiteTensor.Raw (BookSite B C) K :=
  ⟨bookLeg U X Y, inferInstance, bookTensor T⟩

/-- Passing to the raw format preserves the exact coefficient tensor's
nonvanishing. -/
theorem bookRaw_coeff_ne_zero_iff [Zero K] (T : Tensor K U (∀ b, X b) (∀ c, Y c)) :
    (bookRaw T).coeff ≠ 0 ↔ T ≠ 0 := by
  apply not_congr
  constructor
  · intro h
    funext u x y
    exact congrFun h (bookCoordinates.symm (u, x, y))
  · rintro rfl
    rfl

/-- Book-site restrictions are precisely restrictions in the full finite tensor format. -/
theorem bookRaw_restricts_iff [CommSemiring K] [Fintype B] [Fintype C]
    (T : Tensor K U' (∀ b, X' b) (∀ c, Y' c)) (S : Tensor K U (∀ b, X b) (∀ c, Y c)) :
    (bookRaw T).Restricts (bookRaw S) ↔ SiteRestriction T S :=
  (siteRestriction_iff_isRestriction T S).symm

end SpectralBooks
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.SpectralBooks.Crossing
import OAI.LinearAlgebra.SpectralBooks.PermutationStretch

/-!
# Restriction at the common site and the two private site families

A tensor with a distinguished site and two private site families is a tensor on
their disjoint union. This identifies the two matrix descriptions of tensor restriction.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open scoped BigOperators Classical
open MatrixMultiplication.Foundation

section

universe u v

/-- The common site, followed by the two families of private sites. -/
abbrev BookSite (B C : Type*) := Unit ⊕ (B ⊕ C)

/-- The basis at each site, with no grouping of private sites. -/
def bookLeg {B C : Type*} (U : Type u) (X : B → Type u) (Y : C → Type u) :
    BookSite B C → Type u
  | .inl _ => U
  | .inr (.inl b) => X b
  | .inr (.inr c) => Y c

instance {B C : Type*} {U : Type u} {X : B → Type u} {Y : C → Type u}
    [Fintype U] [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)] :
    ∀ i, Fintype (bookLeg U X Y i)
  | .inl _ => inferInstanceAs (Fintype U)
  | .inr (.inl b) => inferInstanceAs (Fintype (X b))
  | .inr (.inr c) => inferInstanceAs (Fintype (Y c))

variable {K B C : Type*}
variable {U : Type u} {X : B → Type u} {Y : C → Type u}
variable {U' : Type v} {X' : B → Type v} {Y' : C → Type v}

/-- Writing a site assignment as its common coordinate and its two families of
private coordinates. -/
def bookCoordinates : (∀ i, bookLeg U X Y i) ≃ U × (∀ b, X b) × (∀ c, Y c) where
  toFun x := (x (.inl ()), fun b => x (.inr (.inl b)), fun c => x (.inr (.inr c)))
  invFun x
    | .inl _ => x.1
    | .inr (.inl b) => x.2.1 b
    | .inr (.inr c) => x.2.2 c
  left_inv := by intro x; funext i; rcases i with _ | b | c <;> rfl
  right_inv := by rintro ⟨u, x, y⟩; rfl

/-- Interpret grouped coefficient arguments as a tensor on the full site set. -/
def bookTensor (T : Tensor K U (∀ b, X b) (∀ c, Y c)) (x : ∀ i, bookLeg U X Y i) : K :=
  T (bookCoordinates x).1 (bookCoordinates x).2.1 (bookCoordinates x).2.2

variable [CommSemiring K] [Fintype B] [Fintype C]
  [Fintype U] [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]

local instance (priority := 4000) {A : Type*} : DecidableEq A := Classical.decEq A

private theorem bookRestriction_sum (M : ∀ i, bookLeg U' X' Y' i → bookLeg U X Y i → K)
    (T : Tensor K U (∀ b, X b) (∀ c, Y c)) (x : ∀ i, bookLeg U' X' Y' i) :
    (∑ a, bookTensor T a * ∏ i, M i (x i) (a i)) = Tensor.restrict (M (.inl ()))
      (fun y' y => ∏ b, M (.inr (.inl b)) (y' b) (y b))
      (fun z' z => ∏ c, M (.inr (.inr c)) (z' c) (z c)) T
      (bookCoordinates x).1 (bookCoordinates x).2.1 (bookCoordinates x).2.2 := by
  let e := bookCoordinates (U := U) (X := X) (Y := Y)
  rw [← Equiv.sum_comp e.symm]
  simp only [Fintype.sum_prod_type, Fintype.prod_sum_type, Fintype.prod_unique,
    Tensor.restrict, bookTensor, e, bookCoordinates, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  ac_rfl

/-- Separate site matrices are equivalent to the restriction preorder on arbitrary
site-indexed tensors, in either direction. -/
theorem siteRestriction_iff_isRestriction
    (T : Tensor K U' (∀ b, X' b) (∀ c, Y' c)) (S : Tensor K U (∀ b, X b) (∀ c, Y c)) :
    SiteRestriction T S ↔ Crossing.IsRestriction (bookTensor T) (bookTensor S) := by
  constructor
  · rintro ⟨A, L, R, rfl⟩
    let M : ∀ i, bookLeg U' X' Y' i → bookLeg U X Y i → K
      | .inl _ => A
      | .inr (.inl b) => L b
      | .inr (.inr c) => R c
    exact ⟨M, fun x => (bookRestriction_sum M S x).symm⟩
  · rintro ⟨M, hM⟩
    refine ⟨M (.inl ()), fun b => M (.inr (.inl b)), fun c => M (.inr (.inr c)), ?_⟩
    funext u x y
    let a := bookCoordinates.symm (u, x, y)
    exact (hM a).trans (bookRestriction_sum M S a)

end

end

end SpectralBooks
end LinearAlgebra
end OAI

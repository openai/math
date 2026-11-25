import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod

namespace OAI
/-! # Evaluation of tensor products of prescribed local matrices

The matrix entry at each site is the product of its entries on the individual
factors. Both formulas allow rectangular local matrices.
-/

open scoped BigOperators Classical

namespace LinearAlgebra.SpectralBooks.SiteTensor

variable {I F : Type*} [Fintype I] [CommSemiring F]

/-- Contracting two factors with their local maps equals contracting their
product with the pointwise Kronecker product of the local maps. -/
theorem table_product_image {A B C D : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    {X : (∀ i, A i) → F} {Y : (∀ i, B i) → F}
    {X' : (∀ i, C i) → F} {Y' : (∀ i, D i) → F}
    (M : ∀ i, C i → A i → F) (N : ∀ i, D i → B i → F)
    (hM : ∀ x, X' x = ∑ a, X a * ∏ i, M i (x i) (a i))
    (hN : ∀ y, Y' y = ∑ b, Y b * ∏ i, N i (y i) (b i))
    (x : ∀ i, C i × D i) :
    X' (fun i => (x i).1) * Y' (fun i => (x i).2) =
      ∑ a : ∀ i, A i × B i, (X (fun i => (a i).1) * Y (fun i => (a i).2)) *
        ∏ i, (M i (x i).1 (a i).1 * N i (x i).2 (a i).2) := by
  classical
  rw [hM, hN, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow I A B).symm _ _ fun a => ?_
  simp only [Finset.prod_mul_distrib]
  ac_rfl

/-- Each site reads its coordinates in every factor. The entry of its grouped
local map is one product over factors, and contracts to the product of the
individual outputs. -/
theorem table_pi_image {J : Type*} [Fintype J] {A B : J → I → Type*}
    [∀ j i, Fintype (A j i)]
    {X : ∀ j, (∀ i, A j i) → F} {Y : ∀ j, (∀ i, B j i) → F}
    (M : ∀ j i, B j i → A j i → F)
    (hM : ∀ j x, Y j x = ∑ a, X j a * ∏ i, M j i (x i) (a i))
    (x : ∀ i j, B j i) :
    (∏ j, Y j (fun i => x i j)) =
      ∑ a : ∀ i j, A j i, (∏ j, X j (fun i => a i j)) *
        ∏ i, ∏ j, M j i (x i j) (a i j) := by
  classical
  simp_rw [hM]
  rw [Fintype.prod_sum]
  refine Fintype.sum_equiv (Equiv.piComm A) _ _ fun a => ?_
  change (∏ j, (X j (a j) * ∏ i, M j i (x i j) (a j i))) =
    (∏ j, X j (a j)) * ∏ i, ∏ j, M j i (x i j) (a j i)
  rw [Finset.prod_mul_distrib]
  exact congrArg (fun v => (∏ j, X j (a j)) * v) Finset.prod_comm

end LinearAlgebra.SpectralBooks.SiteTensor

end OAI

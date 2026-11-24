import OAI.Computability.VPVNP.WireTensor
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Flattening across one tensor party

The row of the matrix is the basis index at the distinguished party and
the column consists of the basis indices at all other parties.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

variable {k J : Type*}

/-- Column indices for the flattening at party `a`. -/
abbrev OtherBasis (a : J) (B : J → Type*) := (j : {j : J // j ≠ a}) → B j

/-- Combine one row index and one column index into a full tensor index. -/
def joinBasis [DecidableEq J] (a : J) {B : J → Type*} (x : B a) (y : OtherBasis a B) :
    (j : J) → B j := (Equiv.piSplitAt a B).symm (x, y)

@[simp] theorem joinBasis_self [DecidableEq J] (a : J) {B : J → Type*}
    (x : B a) (y : OtherBasis a B) : joinBasis a x y a = x := by
  simp [joinBasis, Equiv.piSplitAt_symm_apply]

@[simp] theorem joinBasis_other [DecidableEq J] (a : J) {B : J → Type*}
    (x : B a) (y : OtherBasis a B) (j : {j : J // j ≠ a}) : joinBasis a x y j = y j := by
  simp [joinBasis, Equiv.piSplitAt_symm_apply, j.property]

/-- The matrix of a tensor across one party and its complement. -/
def flattening [DecidableEq J] (a : J) (T : Tensor k J) :
    Matrix (T.Basis a) (OtherBasis a T.Basis) k :=
  .of fun x y => T.coeff (joinBasis a x y)

section Rank

variable [DecidableEq J] [Fintype J] [Field k]

private theorem prod_separate (a : J) (f : J → k) :
    ∏ j, f j = f a * ∏ j : {j : J // j ≠ a}, f j := by
  rw [Fintype.prod_eq_mul_prod_compl a, Finset.prod_subtype _ (by simp : ∀ j, j ∈ ({a}ᶜ : Finset J) ↔ j ≠ a)]

/-- Applying local maps multiplies the flattening on the left and the right.
The right-hand matrix combines the local maps on the complementary parties. -/
theorem flattening_rank_mono (a : J) {T U : Tensor k J} (h : Restricts T U) :
    (flattening a U).rank ≤ (flattening a T).rank := by
  obtain ⟨L, hL⟩ := h
  let A : Matrix (U.Basis a) (T.Basis a) k := .of (L a)
  let B : Matrix (OtherBasis a T.Basis) (OtherBasis a U.Basis) k :=
    .of fun y z => ∏ j : {j : J // j ≠ a}, L j (z j) (y j)
  have heq : flattening a U = A * (flattening a T * B) := by
    ext x z
    change U.coeff (joinBasis a x z) = _
    rw [← hL]
    let f (b : (j : J) → T.Basis j) :=
      (∏ j, L j (joinBasis a x z j) (b j)) * T.coeff b
    unfold applyLocal
    convert_to! ∑ b, f b = _ using 2
    · ext
      simp
    rw [← (Equiv.piSplitAt a T.Basis).symm.sum_comp f, Fintype.sum_prod_type]
    simp only [Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro y _
    change (∏ j, L j (joinBasis a x z j) (joinBasis a i y j)) *
      T.coeff (joinBasis a i y) =
      L a x i * (T.coeff (joinBasis a i y) * ∏ j : {j : J // j ≠ a}, L j (z j) (y j))
    rw [prod_separate a]
    simp [mul_left_comm, mul_comm]
  rw [heq]
  exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_mul_le_left _ _)

/-- Parallel tensor factors flatten to the Kronecker product after regrouping
the two column index tuples. -/
theorem flattening_product_rank (a : J) (T U : Tensor k J) :
    (flattening a (tensorProduct T U)).rank =
      (Matrix.kronecker (flattening a T) (flattening a U)).rank := by
  let e := Equiv.arrowProdEquivProdArrow {j : J // j ≠ a}
    (fun j => T.Basis j) (fun j => U.Basis j)
  have heq : flattening a (tensorProduct T U) =
      (Matrix.kronecker (flattening a T) (flattening a U)).submatrix (Equiv.refl _) e := by
    ext x y
    change T.coeff (fun j => (joinBasis a x y j).1) * U.coeff (fun j => (joinBasis a x y j).2) =
      T.coeff (joinBasis a x.1 (fun j => (y j).1)) * U.coeff (joinBasis a x.2 (fun j => (y j).2))
    congr 2 <;> funext j <;> by_cases hj : j = a
    all_goals first | subst j; simp | simp [joinBasis, Equiv.piSplitAt_symm_apply, hj]
  rw [heq]
  exact Matrix.rank_submatrix _ _ _

/-- A zero coefficient array has zero flattening rank. -/
theorem flattening_zero_rank (a : J) (T : Tensor k J) (h : T.coeff = 0) :
    (flattening a T).rank = 0 := by
  have hz : flattening a T = 0 := by
    ext
    simp [flattening, h]
  rw [hz, Matrix.rank_zero]

/-- Flattening the simple unit gives a one-by-one matrix of rank one. -/
theorem flattening_unit_rank (a : J) : (flattening a (unit (k := k) (J := J))).rank = 1 := by
  let e := Equiv.equivPUnit (OtherBasis a (fun _ => PUnit))
  let M := (1 : Matrix PUnit PUnit k)
  have heq : flattening a (unit (k := k) (J := J)) = M.submatrix (Equiv.refl _) e := by
    ext x y
    change PUnit at x
    change 1 = M x (e y)
    simp [M]
  rw [heq]
  exact (Matrix.rank_submatrix M (Equiv.refl _) e).trans (by simp [M])

end Rank

end WireTensor

end VPVNP
end Computability
end OAI

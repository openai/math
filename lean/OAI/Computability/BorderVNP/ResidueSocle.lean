import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Ring.GeomSum

/-!
# Jacobian determinant on truncated parameter jets

In characteristic `p`, a linear coordinate change multiplies the top monomial
in variables killed by `q = p^u` by its determinant to the power `q - 1`.
This is the parameter-coordinate calculation used when extracting a complete
intersection residue.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

open Matrix
open scoped Matrix

variable {F R ι : Type*} [Field F] [CommRing R] [Algebra F R]
  [Fintype ι] [DecidableEq ι]

private def linearRows (A : Matrix ι ι F) (x : ι → R) (i : ι) : R :=
  ∑ j, algebraMap F R (A i j) * x j

omit [DecidableEq ι] in
private theorem linearRows_mul (A B : Matrix ι ι F) (x : ι → R) :
    linearRows (A * B) x = linearRows A (linearRows B x) := by
  funext i
  simp only [linearRows, Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  exact Finset.sum_comm

private theorem nilpotent_shear (d : ℕ) (x y c : R) (hy : y ^ (d + 1) = 0) :
    (x + c * y) ^ d * y ^ d = x ^ d * y ^ d := by
  obtain ⟨b, hb⟩ := sub_dvd_pow_sub_pow (x + c * y) x d
  rw [add_sub_cancel_left] at hb
  rw [← sub_eq_zero, ← sub_mul, hb, show c * y * b * y ^ d = c * b * y ^ (d+1) by ring,
    hy, mul_zero]

/-- The top monomial of the `q`-truncated coordinate ring transforms by `det(A)^(q-1)`.
The target may be any commutative algebra with the specified nilpotent coordinates. -/
theorem socle_determinant (p u : ℕ) [ExpChar R p] (A : Matrix ι ι F)
    (x : ι → R) (hx : ∀ i, x i ^ p ^ u = 0) :
    (∏ i, (∑ j, algebraMap F R (A i j) * x j) ^ (p ^ u - 1)) =
      algebraMap F R (A.det ^ (p ^ u - 1)) * ∏ i, x i ^ (p ^ u - 1) := by
  let d := p ^ u - 1
  have hq : d + 1 = p ^ u := Nat.sub_add_cancel (expChar_pow_pos R p u)
  let P := fun B : Matrix ι ι F ↦ ∀ (y : ι → R), (∀ i, y i ^ p ^ u = 0) →
    (∏ i, (linearRows B y i) ^ d) = algebraMap F R (B.det ^ d) * ∏ i, y i ^ d
  refine Matrix.diagonal_transvection_induction P A ?_ ?_ ?_ x hx
  · intro D _ y _
    have hd (i : ι) : linearRows (diagonal D) y i = algebraMap F R (D i) * y i := by
      simp [linearRows, diagonal_apply, apply_ite, ite_mul]
    simp only [hd, mul_pow, Finset.prod_mul_distrib, Matrix.det_diagonal, map_pow, map_prod,
      Finset.prod_pow]
  · intro t y hy
    have hrow (i : ι) : linearRows t.toMatrix y i =
        if i = t.i then y i + algebraMap F R t.c * y t.j else y i := by
      by_cases hi : i = t.i
      · subst i
        simp [linearRows, TransvectionStruct.toMatrix, transvection, single_apply, one_apply,
          add_mul, Finset.sum_add_distrib]
        rw [Finset.sum_eq_single t.j]
        · simp
        · intro j _ hj
          simp [Ne.symm hj]
        · simp
      · simp [linearRows, TransvectionStruct.toMatrix, transvection, one_apply, hi, Ne.symm hi,
          apply_ite, ite_mul]
    rw [t.det, one_pow, map_one, one_mul]
    let S : Finset ι := Finset.univ.erase t.i
    have hj : t.j ∈ S := Finset.mem_erase.mpr ⟨t.hij.symm, Finset.mem_univ _⟩
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t.i),
      ← Finset.mul_prod_erase _ (fun i ↦ y i ^ d) (Finset.mem_univ t.i), hrow t.i, ite_eq_left rfl]
    have rest : (∏ i ∈ S, (linearRows t.toMatrix y i) ^ d) = ∏ i ∈ S, y i ^ d := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hrow, ite_eq_right (Finset.mem_erase.mp hi).1]
    rw [rest, ← Finset.mul_prod_erase S (fun i ↦ y i ^ d) hj, ← mul_assoc, ← mul_assoc,
      nilpotent_shear d _ _ _ (hq ▸ hy t.j)]
  · intro A B hA hB y hy
    have hb (i : ι) : linearRows B y i ^ p ^ u = 0 := by
      change iterateFrobenius R p u (∑ j, algebraMap F R (B i j) * y j) = 0
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro j _
      change (algebraMap F R (B i j) * y j) ^ p ^ u = 0
      rw [mul_pow, hy j, mul_zero]
    dsimp only [P] at *
    rw [linearRows_mul, hA _ hb, hB _ hy, Matrix.det_mul, mul_pow, map_mul, mul_assoc]

end Residue

end BorderVNP
end Computability
end OAI

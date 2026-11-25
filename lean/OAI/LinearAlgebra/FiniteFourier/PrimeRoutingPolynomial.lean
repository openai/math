import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! # The charged-rectangle coefficients

On distances h divisible by ℓ the charged rectangles must distinguish h=0
from every other such distance. Choose coefficients in the basis of binomials
in the number of equal positions. Its interpolation matrix at step ℓ is
invertible over every commutative ring in which ℓ is a unit.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open Polynomial Matrix

private theorem choose_progression_expansion {R : Type*} [CommRing R] (s ℓ r t : ℕ) (hr : r ≤ t) :
    (1 + X : R[X])^(s+ℓ*r) = ∑ d : Fin (t+1), C (r.choose d.val : R) *
      ((1 + X)^s * (((1+X)^ℓ-1)^d.val)) := by
  let Y := ((1+X : R[X])^ℓ-1)
  have hpow := add_pow Y 1 r
  rw [Fin.sum_univ_eq_sum_range (f := fun d : ℕ =>
    C (r.choose d : R) * ((1 + X : R[X])^s * (((1 + X)^ℓ-1)^d)))]
  calc
    _ = (1+X)^s * (Y+1)^r := by rw [pow_add, pow_mul]; simp [Y]
    _ = ∑ d ∈ Finset.range (r+1), C (r.choose d : R) * ((1+X)^s * Y^d) := by
      rw [hpow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      simp [mul_comm, mul_left_comm]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro i _ hi
      simp [Nat.choose_eq_zero_of_lt (by simpa using hi : r < i)]

/-- The coefficient matrix of the binomial basis at arithmetic-progression
arguments is invertible over any coefficient ring where the step is a unit. -/
theorem exists_charged_coefficients (R : Type*) [CommRing R] (s ℓ t : ℕ) (hℓ : IsUnit (ℓ : R)) :
    ∃ w : Fin (t+1) → R, ∀ r ≤ t,
      ∑ j : Fin (t+1), ((s+ℓ*r).choose j.val : R) * w j = if r = t then 1 else 0 := by
  classical
  let Z := (1 + X : R[X])^s
  let Y := (1 + X : R[X])^ℓ - 1
  let Q := Y.divX
  have hy0 : Y.coeff 0 = 0 := by simp [Y, coeff_one_add_X_pow]
  have hY : X * Q = Y := by simpa [Q, hy0] using X_mul_divX_add Y
  have hQ : Q.coeff 0 = (ℓ : R) := by simp [Q, Y, coeff_divX, coeff_one_add_X_pow, Polynomial.coeff_one]
  let B : Matrix (Fin (t+1)) (Fin (t+1)) R := fun i j => (Z * Y^i.val).coeff j.val
  have hB (i j : Fin (t+1)) : B i j = ((Z * Q ^ i.val) * X^i.val).coeff j.val := by
    dsimp only [B]
    rw [← hY, mul_pow]
    congr 1
    ac_rfl
  have htri : B.IsUpperTriangular := by
    intro i j hj
    rw [hB, coeff_mul_X_pow']
    simp [show ¬ i.val ≤ j.val from Nat.not_le.mpr hj]
  have hdiag (i : Fin (t+1)) : B i i = (ℓ:R)^i.val := by
    rw [hB, coeff_mul_X_pow']
    simp only [le_rfl, ite_true, Nat.sub_self, Polynomial.mul_coeff_zero, Z, coeff_one_add_X_pow,
      Nat.choose_zero_right, Nat.cast_one, one_mul]
    change (Polynomial.constantCoeff (R := R)) (Q^i.val) = _
    rw [map_pow]
    exact congrArg (fun x : R => x^i.val) hQ
  have hdet : IsUnit B.det := by
    rw [Matrix.det_of_isUpperTriangular htri]
    simp_rw [hdiag]
    exact IsUnit.prod_univ_iff.mpr (fun i => hℓ.pow _)
  let w := B⁻¹ *ᵥ Pi.single (Fin.last t) 1
  have hw : B *ᵥ w = Pi.single (Fin.last t) 1 := by
    rw [show B *ᵥ w = (B * B⁻¹) *ᵥ Pi.single (Fin.last t) 1 from Matrix.mulVec_mulVec ..,
      Matrix.mul_nonsing_inv B hdet, Matrix.one_mulVec]
  refine ⟨w, fun r hr => ?_⟩
  have hcoef (j : Fin (t+1)) : ((s+ℓ*r).choose j.val : R) =
      ∑ d : Fin (t+1), (r.choose d.val : R) * B d j := by
    rw [← coeff_one_add_X_pow, choose_progression_expansion s ℓ r t hr, finsetSum_coeff]
    simp [B, Z, Y]
  simp_rw [hcoef, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  change ∑ i : Fin (t+1), ((r.choose i.val : ℕ) : R) * (B *ᵥ w) i = _
  rw [hw]
  simp [Pi.single_apply, mul_ite, Fin.last]
  by_cases he : r = t
  · simp [he]
  · simp [he, Nat.choose_eq_zero_of_lt (by omega : r < t)]

end

end

end FiniteFourier
end LinearAlgebra
end OAI

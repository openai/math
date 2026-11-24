import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring

/-!
# Formal Schur factors of the reverse characteristic polynomial

Appendix D.2 of *VP and VNP differ over every field* factors `det (1 - uM)`
over formal power series by successively deleting the first row and column.
The geometric inverse of a trailing matrix pencil has the powers of that
matrix as its coefficients.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery

open scoped BigOperators Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The power-series matrix pencil whose inverse encodes all matrix powers. -/
noncomputable def formalPencil (M : Matrix ι ι R) : Matrix ι ι (PowerSeries R) :=
  1 - (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C

/-- The entrywise series of powers of the matrix. -/
noncomputable def formalResolvent (M : Matrix ι ι R) : Matrix ι ι (PowerSeries R) :=
  Matrix.of (fun i j => PowerSeries.mk (fun h => (M ^ h) i j))

@[simp] theorem coeff_formalResolvent (M : Matrix ι ι R) (h : ℕ) (i j : ι) :
    PowerSeries.coeff h (formalResolvent M i j) = (M ^ h) i j :=
  PowerSeries.coeff_mk h (fun k => (M ^ k) i j)

theorem formalResolvent_mul_formalPencil (M : Matrix ι ι R) :
    formalResolvent M * formalPencil M = 1 := by
  rw [formalPencil, mul_sub, mul_one, Matrix.mul_smul]
  apply Matrix.ext
  intro i j
  apply PowerSeries.ext
  intro h
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, coeff_formalResolvent]
  cases h with
  | zero =>
    rw [PowerSeries.coeff_zero_X_mul, sub_zero, pow_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp [PowerSeries.coeff_one]
  | succ h =>
    rw [PowerSeries.coeff_succ_X_mul, pow_succ, Matrix.mul_apply, Matrix.mul_apply, map_sum]
    simp only [Matrix.map_apply, PowerSeries.coeff_mul_C, coeff_formalResolvent, sub_self]
    rw [Matrix.one_apply]
    split_ifs <;> simp [PowerSeries.coeff_one]

theorem formalPencil_mul_formalResolvent (M : Matrix ι ι R) :
    formalPencil M * formalResolvent M = 1 :=
  mul_eq_one_comm.mp (formalResolvent_mul_formalPencil M)

/-- Invertibility witness for the formal matrix pencil, with its formal resolvent as the
inverse. -/
@[instance_reducible] noncomputable def pencilInvertible (M : Matrix ι ι R) :
    Invertible (formalPencil M) where
  invOf := formalResolvent M
  invOf_mul_self := formalResolvent_mul_formalPencil M
  mul_invOf_self := formalPencil_mul_formalResolvent M

/-- Every coefficient of the inverse pencil is an entry of a finite matrix power. -/
theorem coeff_formalPencil_inv (M : Matrix ι ι R) (h : ℕ) (i j : ι) :
    PowerSeries.coeff h ((formalPencil M)⁻¹ i j) = (M ^ h) i j := by
  rw [Matrix.inv_eq_left_inv (formalResolvent_mul_formalPencil M), coeff_formalResolvent]

variable {n : ℕ}

/-- The Schur complement obtained by deleting the first row and column. -/
noncomputable def headFactor (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : PowerSeries R :=
  1 - PowerSeries.X * PowerSeries.C (M 0 0) - PowerSeries.X ^ 2 *
    ∑ i : Fin n, ∑ j : Fin n, PowerSeries.C (M 0 i.succ) *
      formalResolvent (M.submatrix Fin.succ Fin.succ) i j * PowerSeries.C (M j.succ 0)

theorem det_formalPencil_succ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (formalPencil M).det = headFactor M * (formalPencil (M.submatrix Fin.succ Fin.succ)).det := by
  classical
  let _ := pencilInvertible (M.submatrix Fin.succ Fin.succ)
  have hinv : ⅟(formalPencil (M.submatrix Fin.succ Fin.succ)) =
      formalResolvent (M.submatrix Fin.succ Fin.succ) := rfl
  let e : Unit ⊕ Fin n ≃ Fin (n + 1) :=
    (Equiv.sumComm _ _).trans ((Equiv.optionEquivSumPUnit _).symm.trans (finSuccEquiv n).symm)
  let a : Matrix Unit Unit (PowerSeries R) :=
    Matrix.of fun _ _ => 1 - PowerSeries.X * PowerSeries.C (M 0 0)
  let b : Matrix Unit (Fin n) (PowerSeries R) :=
    Matrix.of fun _ j => -(PowerSeries.X * PowerSeries.C (M 0 j.succ))
  let c : Matrix (Fin n) Unit (PowerSeries R) :=
    Matrix.of fun i _ => -(PowerSeries.X * PowerSeries.C (M i.succ 0))
  have hblock : (formalPencil M).submatrix e e =
      Matrix.fromBlocks a b c (formalPencil (M.submatrix Fin.succ Fin.succ)) := by
    ext i j
    cases i <;> cases j <;>
      simp [e, a, b, c, formalPencil, Matrix.one_apply, smul_eq_mul, Ne.symm (Fin.succ_ne_zero _)]
  rw [← Matrix.det_submatrix_equiv_self e (formalPencil M), hblock, Matrix.det_fromBlocks₂₂,
    hinv, Matrix.det_unique (a - b * formalResolvent (M.submatrix Fin.succ Fin.succ) * c), mul_comm]
  congr 1
  simp only [Matrix.sub_apply, Matrix.mul_apply, a, b, c, Matrix.of_apply, headFactor]
  congr 1
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

section TrailingIndices

variable {R A : Type*}

/-- Evaluate a local rule on each trailing submatrix by repeatedly dropping the first index. -/
private def peelFactors (f : ∀ {n : ℕ}, Matrix (Fin (n + 1)) (Fin (n + 1)) R → A) :
    ∀ {n : ℕ}, Matrix (Fin n) (Fin n) R → Fin n → A
  | 0, _ => Fin.elim0
  | _ + 1, M => Fin.cons (f M) (peelFactors f (M.submatrix Fin.succ Fin.succ))

/-- Place the indices of the trailing principal submatrix in the full matrix. -/
def suffixIndex {n : ℕ} (i : Fin n) (j : Fin ((n - i.val - 1) + 1)) : Fin n :=
  ⟨j.val + i.val, by have := j.isLt; have := i.isLt; omega⟩

private theorem peelFactors_eq_of_size
    (f : ∀ {n : ℕ}, Matrix (Fin (n + 1)) (Fin (n + 1)) R → A)
    {n m : ℕ} (M : Matrix (Fin n) (Fin n) R) (i : Fin n) (h : i.val + (m + 1) = n) :
    peelFactors f M i = f (M.submatrix
      (fun j : Fin (m + 1) => ⟨j.val + i.val, by have := j.isLt; omega⟩)
      (fun j : Fin (m + 1) => ⟨j.val + i.val, by have := j.isLt; omega⟩)) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.zero_add, Nat.add_right_cancel_iff] at h
      subst m
      change f M = f _
      congr 1
    | succ i =>
      have h' : i.val + (m + 1) = n := by simp only [Fin.val_succ] at h; omega
      change peelFactors f (M.submatrix Fin.succ Fin.succ) i = _
      rw [ih (M.submatrix Fin.succ Fin.succ) i h']
      congr 1

private theorem peelFactors_apply
    (f : ∀ {n : ℕ}, Matrix (Fin (n + 1)) (Fin (n + 1)) R → A)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    peelFactors f M i = f (M.submatrix (suffixIndex i) (suffixIndex i)) :=
  peelFactors_eq_of_size f M i (by have := i.isLt; omega)

end TrailingIndices

theorem coe_charpolyRev (M : Matrix ι ι R) :
    (M.charpolyRev : PowerSeries R) = (formalPencil M).det := by
  change Polynomial.coeToPowerSeries.ringHom (M.charpolyRev) = _
  rw [Matrix.charpolyRev, RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change Polynomial.coeToPowerSeries.ringHom
    ((1 - (Polynomial.X : Polynomial R) • M.map Polynomial.C) i j) = _
  rw [Matrix.sub_apply, map_sub, Matrix.smul_apply, smul_eq_mul, map_mul]
  simp [formalPencil, Matrix.one_apply, smul_eq_mul]

/-- The degree-zero and degree-one terms of a Schur factor come from the diagonal.
Each higher coefficient queries exactly one power of the trailing matrix. -/
theorem coeff_headFactor (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (u : ℕ) :
    PowerSeries.coeff u (headFactor M) = match u with
      | 0 => 1
      | 1 => -M 0 0
      | h + 2 => -(∑ i : Fin n, ∑ j : Fin n, M 0 i.succ *
          (M.submatrix Fin.succ Fin.succ ^ h) i j * M j.succ 0) := by
  rcases u with _ | _ | h
  · simp [headFactor]
  · simp [headFactor, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X]
  · change PowerSeries.coeff (h + 2) _ = _
    simp [headFactor, PowerSeries.coeff_X]

private theorem det_eq_peelProduct (M : Matrix (Fin n) (Fin n) R) :
    (formalPencil M).det = ∏ i, peelFactors (fun {_} => headFactor) M i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [det_formalPencil_succ, ih, Fin.prod_univ_succ]
    rfl

/-- Every factor of the reverse characteristic polynomial is obtained by a direct
index shift to the trailing principal submatrix beginning at the given row. -/
theorem charpolyRev_eq_schurProduct (M : Matrix (Fin n) (Fin n) R) :
    (M.charpolyRev : PowerSeries R) =
      ∏ i : Fin n, headFactor (M.submatrix (suffixIndex i) (suffixIndex i)) := by
  rw [coe_charpolyRev, det_eq_peelProduct]
  simp only [peelFactors_apply]

end RankQuery

end VPVNP
end Computability
end OAI

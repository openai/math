import OAI.LinearAlgebra.FiniteFourier.Feedback
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # The rational transfer and its specializations

The common denominator is the determinant of the delayed state pencil. Its
value is one at zero, and is nonzero at one precisely for regular systems.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Feedback

open Matrix Polynomial
noncomputable section

variable {K I O : Type*} [Field K] {s : ℕ} (F : Feedback K I O s)

/-- The polynomial state pencil. -/
def statePencil : Matrix (Fin s) (Fin s) K[X] :=
  1 - (X : K[X]) • F.stateMatrix.map C

/-- A common denominator, equal to one when the delays vanish. -/
def transferDenom : K[X] := F.statePencil.det

/-- The common-denominator numerator for the rational input-output matrix. -/
def transferNumer : Matrix O I K[X] :=
  F.transferDenom • F.readInput.map C +
    F.readState.map C * F.statePencil.adjugate * ((X : K[X]) • F.inputMatrix.map C)

/-- The rational transfer matrix over the one-variable function field. -/
def rationalTransfer : Matrix O I (RatFunc K) := fun i j =>
  algebraMap K[X] (RatFunc K) (F.transferNumer i j) /
    algebraMap K[X] (RatFunc K) F.transferDenom

variable {R : Type*} [CommRing R]

theorem map_statePencil (φ : K[X] →+* R) :
    F.statePencil.map φ = 1 - φ X • F.stateMatrix.map (φ.comp C) := by
  ext i j
  simp [statePencil, Matrix.one_apply]
  exact mul_comm _ _

theorem map_transferDenom (φ : K[X] →+* R) :
    φ F.transferDenom = (1 - φ X • F.stateMatrix.map (φ.comp C)).det := by
  simpa only [transferDenom, RingHom.map_det, RingHom.mapMatrix_apply] using
    congrArg Matrix.det (F.map_statePencil φ)

private theorem map_poly_smul {m n : Type*} (φ : K[X] →+* R) (p : K[X])
    (M : Matrix m n K[X]) :
    (p • M).map φ = φ p • M.map φ := by
  ext; simp

theorem map_transferNumer (φ : K[X] →+* R) :
    F.transferNumer.map φ = φ F.transferDenom • F.readInput.map (φ.comp C) +
      F.readState.map (φ.comp C) * (F.statePencil.map φ).adjugate *
        (φ X • F.inputMatrix.map (φ.comp C)) := by
  simp only [transferNumer, Matrix.map_add _ (map_add φ), Matrix.map_mul, map_poly_smul,
    ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
  rfl

private theorem map_eval_C {m n : Type*} (M : Matrix m n K) (z : K) :
    M.map ((evalRingHom z).comp C) = M := by
  ext; simp

theorem eval_transferDenom (z : K) :
    F.transferDenom.eval z = (1 - z • F.stateMatrix).det := by
  simpa only [coe_evalRingHom, eval_X, map_eval_C] using
    F.map_transferDenom (evalRingHom z)

@[simp] theorem eval_zero_transferDenom : F.transferDenom.eval 0 = 1 := by
  simp [eval_transferDenom]

theorem eval_one_transferDenom : F.transferDenom.eval 1 = (1 - F.stateMatrix).det := by
  simp [eval_transferDenom]

theorem transferDenom_ne_zero : F.transferDenom ≠ 0 := by
  intro h
  simpa [h] using F.eval_zero_transferDenom

/-- Regularity at any point where the common denominator survives, for the
reduced denominators of every individual rational entry. -/
theorem rationalTransfer_regularAt {z : K} (hz : F.transferDenom.eval z ≠ 0) (o : O) (i : I) :
    (F.rationalTransfer o i).denom.eval z ≠ 0 := by
  obtain ⟨d, hd⟩ := RatFunc.denom_div_dvd (F.transferNumer o i) F.transferDenom
  intro hr
  apply hz
  change (algebraMap K[X] (RatFunc K) (F.transferNumer o i) /
    algebraMap K[X] (RatFunc K) F.transferDenom).denom.eval z = 0 at hr
  rw [hd, eval_mul, hr, zero_mul]

theorem rationalTransfer_regular_zero (o : O) (i : I) :
    (F.rationalTransfer o i).denom.eval 0 ≠ 0 :=
  F.rationalTransfer_regularAt (by simp) o i

theorem rationalTransfer_regular_one (h : F.Regular) (o : O) (i : I) :
    (F.rationalTransfer o i).denom.eval 1 ≠ 0 :=
  F.rationalTransfer_regularAt (by rwa [eval_one_transferDenom]) o i

/-- Evaluation of the nonreduced common-denominator expression is valid at
all regular points of the state pencil. -/
theorem eval_rationalTransfer_entry {z : K} (hz : F.transferDenom.eval z ≠ 0)
    (o : O) (i : I) :
    RatFunc.eval (RingHom.id K) z (F.rationalTransfer o i) =
      (F.transferNumer o i).eval z / F.transferDenom.eval z := by
  have h := (RatFunc.num_mul_eq_mul_denom_iff F.transferDenom_ne_zero).mpr
    (show F.rationalTransfer o i = _ from rfl)
  have he := congrArg (eval z) h
  simp only [eval_mul] at he
  change (F.rationalTransfer o i).num.eval z / (F.rationalTransfer o i).denom.eval z = _
  exact (div_eq_div_iff (F.rationalTransfer_regularAt hz o i) hz).mpr he

/-- A solution of the delayed state equations, over any commutative target
ring, gives the same polynomial transfer after clearing the common denominator.
In particular the target ring may be the formal power series ring. -/
theorem clear_transfer_of_stateEquation (φ : K[X] →+* R) (V : Matrix (Fin s) I R)
    (hV : F.statePencil.map φ * V = φ X • F.inputMatrix.map (φ.comp C)) :
    φ F.transferDenom •
      (F.readInput.map (φ.comp C) + F.readState.map (φ.comp C) * V) =
        F.transferNumer.map φ := by
  rw [F.map_transferNumer, ← hV, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ V,
    Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_add]
  have hdet : φ F.transferDenom = (F.statePencil.map φ).det :=
    φ.map_det F.statePencil
  rw [hdet]

section Field

variable {L : Type*} [Field L]

/-- The normalized numerator is the resolvent formula of the manuscript
whenever the denominator is nonzero. -/
theorem normalized_transferNumer (φ : K[X] →+* L) (h : φ F.transferDenom ≠ 0) :
    (φ F.transferDenom)⁻¹ • F.transferNumer.map φ =
      F.readInput.map (φ.comp C) + F.readState.map (φ.comp C) *
        (F.statePencil.map φ)⁻¹ * (φ X • F.inputMatrix.map (φ.comp C)) := by
  have hdet : φ F.transferDenom = (F.statePencil.map φ).det :=
    φ.map_det F.statePencil
  rw [F.map_transferNumer, smul_add, smul_smul, inv_mul_cancel₀ h, one_smul,
    Matrix.inv_def, Ring.inverse_eq_inv, ← hdet, Matrix.mul_smul (F.readState.map (φ.comp C)) _ _, Matrix.smul_mul]

/-- The pencil has nonzero determinant over the rational function field,
including when its specialization at one is singular. -/
theorem det_rational_statePencil_ne_zero :
    (1 - (RatFunc.X : RatFunc K) • F.stateMatrix.map RatFunc.C).det ≠ 0 := by
  let φ := algebraMap K[X] (RatFunc K)
  have h := F.map_transferDenom φ
  have hc : φ.comp C = (RatFunc.C : K →+* RatFunc K) := by ext; simp [φ]
  rw [hc] at h
  exact h ▸ RatFunc.algebraMap_ne_zero F.transferDenom_ne_zero

/-- Identity of matrices over the rational function field. -/
theorem rationalTransfer_eq_resolvent :
    F.rationalTransfer = F.readInput.map RatFunc.C + F.readState.map RatFunc.C *
      (1 - (RatFunc.X : RatFunc K) • F.stateMatrix.map RatFunc.C)⁻¹ *
        ((RatFunc.X : RatFunc K) • F.inputMatrix.map RatFunc.C) := by
  let φ := algebraMap K[X] (RatFunc K)
  have hφ : φ F.transferDenom ≠ 0 := RatFunc.algebraMap_ne_zero F.transferDenom_ne_zero
  have h := F.normalized_transferNumer φ hφ
  rw [F.map_statePencil] at h
  have hc : φ.comp C = (RatFunc.C : K →+* RatFunc K) := by ext; simp [φ]
  rw [hc] at h
  calc
    _ = (φ F.transferDenom)⁻¹ • F.transferNumer.map φ := by
      ext; simp [rationalTransfer, φ, div_eq_mul_inv, mul_comm]
    _ = _ := h

/-- The delayed rational transfer evaluated at any regular scalar delay. -/
theorem eval_rationalTransfer {z : K} (hz : F.transferDenom.eval z ≠ 0) :
    F.rationalTransfer.map (RatFunc.eval (RingHom.id K) z) =
      F.readInput + F.readState * (1 - z • F.stateMatrix)⁻¹ * (z • F.inputMatrix) := by
  have h := F.normalized_transferNumer (evalRingHom z) hz
  rw [F.map_statePencil] at h
  simp only [map_eval_C, coe_evalRingHom, eval_X] at h
  convert h using 1
  ext o i
  simp [eval_rationalTransfer_entry F hz, div_eq_mul_inv, mul_comm]

@[simp] theorem eval_zero_rationalTransfer :
    F.rationalTransfer.map (RatFunc.eval (RingHom.id K) 0) = F.readInput := by
  simp [F.eval_rationalTransfer (z := 0) (by simp)]

theorem eval_one_rationalTransfer (h : F.Regular) :
    F.rationalTransfer.map (RatFunc.eval (RingHom.id K) 1) = F.matrix := by
  simp [F.eval_rationalTransfer (z := 1) (by rwa [eval_one_transferDenom]), matrix]

end Field

end
end Feedback

end FiniteFourier
end LinearAlgebra
end OAI

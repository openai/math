import OAI.LinearAlgebra.FiniteFourier.Feedback.FeedbackTransfer
import OAI.LinearAlgebra.FiniteFourier.Feedback.WalkCount

/-! # Taylor series of the rational transfer

The recursively enumerated walks give the Taylor coefficients of the common
rational transfer. Clearing its denominator yields an equality of formal power
series without choosing any Laurent series expansion.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Feedback

open Matrix PowerSeries
noncomputable section

variable {K I O : Type*} [Field K] {s : ℕ} (F : Feedback K I O s)

/-- The series of walks ending at each state. -/
def stateSeries : Matrix (Fin s) I (PowerSeries K) := fun a i => F.signalSeries (.inr a) i

private theorem coeff_const_mul {ι κ τ : Type*} [Fintype κ] (M : Matrix ι κ K)
    (V : Matrix κ τ (PowerSeries K)) (n : ℕ) (a : ι) (i : τ) :
    coeff n ((M.map C * V) a i) = (M * V.map (coeff n)) a i := by
  simp [Matrix.mul_apply, coeff_C_mul]

private theorem stateSeries_zero : F.stateSeries.map (coeff 0) = 0 := by
  ext a i
  simp [stateSeries, signalSeries, signalCoeff]

private theorem stateSeries_succ (n : ℕ) :
    F.stateSeries.map (coeff (n + 1)) = F.stateMatrix ^ n * F.inputMatrix := by
  ext a i
  simpa [stateSeries, signalSeries] using F.signalCoeff_state n a i

/-- The walk series satisfies the delayed simultaneous state equations. -/
theorem stateSeries_equation :
    F.stateSeries = (X : PowerSeries K) •
      (F.stateMatrix.map C * F.stateSeries + F.inputMatrix.map C) := by
  ext a i n
  cases n with
  | zero =>
    change coeff 0 (F.signalSeries (.inr a) i) = coeff 0 (X * _)
    simp [signalSeries, signalCoeff]
  | succ n =>
    change coeff (n + 1) (F.stateSeries a i) =
      coeff (n + 1) (X * ((F.stateMatrix.map C * F.stateSeries) a i + C (F.inputMatrix a i)))
    change (F.stateSeries.map (coeff (n + 1))) a i = _
    rw [F.stateSeries_succ, coeff_succ_X_mul, map_add, coeff_const_mul, coeff_C]
    cases n with
    | zero => rw [F.stateSeries_zero]; simp
    | succ n => simp [F.stateSeries_succ, pow_succ' _ n, Matrix.mul_assoc]

/-- The series of walks to each output consists of its direct input term and
the selected state readout. -/
theorem delaySeries_eq_readout :
    F.delaySeries = F.readInput.map C + F.readState.map C * F.stateSeries := by
  ext o i n
  change coeff n (F.delaySeries o i) =
    coeff n (C (F.readInput o i) + (F.readState.map C * F.stateSeries) o i)
  rw [map_add, coeff_C, coeff_const_mul]
  cases n with
  | zero => rw [F.stateSeries_zero, F.coeff_zero_delaySeries]; simp
  | succ n => simp [F.stateSeries_succ, F.coeff_succ_delaySeries, Matrix.mul_assoc]

/-- The polynomial common denominator times the walk series is exactly the
polynomial numerator, embedded into formal power series. -/
theorem transferDenom_mul_delaySeries (o : O) (i : I) :
    (F.transferDenom : PowerSeries K) * F.delaySeries o i =
      ((F.transferNumer o i : Polynomial K) : PowerSeries K) := by
  let φ := Polynomial.coeToPowerSeries.ringHom (R := K)
  have hc : φ.comp Polynomial.C = (C : K →+* PowerSeries K) := by
    apply RingHom.ext
    exact Polynomial.coe_C
  have hx : φ Polynomial.X = X := Polynomial.coe_X
  have hV : F.statePencil.map φ * F.stateSeries =
      φ Polynomial.X • F.inputMatrix.map (φ.comp Polynomial.C) := by
    rw [F.map_statePencil, hc, hx, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
      sub_eq_iff_eq_add', ← smul_add]
    exact F.stateSeries_equation
  have h := F.clear_transfer_of_stateEquation φ F.stateSeries hV
  rw [hc, ← F.delaySeries_eq_readout] at h
  exact congrFun (congrFun h o) i

/-- Explicit Taylor expansion using the common denominator, whose constant
term is one. -/
theorem delaySeries_eq_quotient (o : O) (i : I) :
    F.delaySeries o i = (F.transferNumer o i : PowerSeries K) *
      (F.transferDenom : PowerSeries K)⁻¹ := by
  have hu : constantCoeff (F.transferDenom : PowerSeries K) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero, F.eval_zero_transferDenom]
    exact one_ne_zero
  rw [← F.transferDenom_mul_delaySeries,
    mul_comm (F.transferDenom : PowerSeries K) (F.delaySeries o i), mul_assoc,
    PowerSeries.mul_inv_cancel _ hu, mul_one]

end
end Feedback

end FiniteFourier
end LinearAlgebra
end OAI

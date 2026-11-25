import OAI.LinearAlgebra.FiniteFourier.PhasePrice

/-! # A common normalized point for a Fourier rectangle

At distinct corners the spectral placement supplies a single spectral point
for all matrix formats. The diagonal semiperimeter gives its normalization.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

variable {K : Type*} [Field K]

private theorem rectangle_injective {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    Function.Injective (rectangleSites (2*s) (2*c)) := by
  intro i j hij
  have hx := congrArg (fun p : Plane ↦ p 0) hij
  have hy := congrArg (fun p : Plane ↦ p 1) hij
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; first
    | change -(2*c)/2 = (2*c)/2 at hx; linarith
    | change (2*c)/2 = -(2*c)/2 at hx; linarith
    | change -(2*s)/2 = (2*s)/2 at hy; linarith
    | change (2*s)/2 = -(2*s)/2 at hy; linarith)

/-- The spectral point and all rectangle matrix values agree on every finite
matrix format, with the usual zero value at the zero matrix. -/
theorem exists_rectangle_point (P : SpectralPlacementPrices K Plane) {s c : ℝ}
    (hs : 0 < s) (hc : 0 < c)
    (hnormal : P.price (Raw.diagonal (Fin 4) K (Fin 2)) (rectangleSites (2*s) (2*c)) = 2*(c+s)) :
    ∃ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 4) K → _ → Prop),
      ∀ (O I : Type) [Fintype O] [Fintype I] (M : Matrix O I K),
        (φ.val (ofRaw (phaseRaw M)) : ℝ) = rectangleValue (fourierPhasePrice P) M s c := by
  let x : Fin 4 ↪ Plane := ⟨rectangleSites (2*s) (2*c), rectangle_injective hs hc⟩
  obtain ⟨φ, hφ⟩ := P.normalized x
  refine ⟨φ, ?_⟩
  intro O I _ _ M
  by_cases hM : M = 0
  · have hzero : (phaseRaw M).coeff = 0 := not_not.mp fun h ↦ phaseRaw_coeff_ne_zero.mp h hM
    rw [(ofRaw_eq_zero_iff _).mpr hzero, φ.property.1, rectangleValue, ite_eq_left hM]
    rfl
  · rw [rectangleValue, ite_eq_right hM]
    change _ = 2 ^ (P.price (phaseRaw M) x / (2 * (c+s)))
    have hd : P.price (Raw.diagonal (Fin 4) K (Fin 2)) x = 2*(c+s) := hnormal
    rw [hφ _ (phaseRaw_coeff_ne_zero.mpr hM), hd, mul_div_cancel_left₀ _ (by positivity),
      Real.rpow_logb (by norm_num) (by norm_num)]
    exact_mod_cast zero_lt_one.trans_le (one_le_raw_spectralValue φ _ (phaseRaw_coeff_ne_zero.mpr hM))

end

end

end FiniteFourier
end LinearAlgebra
end OAI

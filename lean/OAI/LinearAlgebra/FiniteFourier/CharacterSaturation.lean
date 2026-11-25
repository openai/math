import OAI.LinearAlgebra.FiniteFourier.CopyMove
import OAI.LinearAlgebra.FiniteFourier.CopySwap
import OAI.LinearAlgebra.FiniteFourier.PhaseCommonLabels
import OAI.LinearAlgebra.FiniteFourier.Saturation

/-! # The character-table price on every rectangle

This section applies the spectral plane and copying hypotheses of the
manuscript to the actual full Fourier matrix over the input field. All
aspect ratios, including collapsed sides, are allowed.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

/-- The additional geometric properties of the planar prices in the
spectral-plane and copying theorem. -/
structure FourierPlaneLaws {K : Type*} [Field K] (P : SpectralPlacementPrices K Plane) : Prop where
  sublinear : ∀ {I : Type} [Fintype I] (T : Raw.{0} I K), SublinearPrice (P.price T)
  flat : ∀ (S : Finset Plane) (hS : S.Nonempty), P.diagonal S = meanWidth S hS

variable {K : Type*} [Field K] {G : Type} [AddCommGroup G] [Fintype G]

theorem fourierMatrix_ne_zero (G : Type) [AddCommGroup G] (K : Type*) [Field K] :
    fourierMatrix G K ≠ 0 := by
  intro h
  have hv := congrFun (congrFun h (1 : Character G K)) (0 : G)
  simp [fourierMatrix] at hv

/-- Over a field in any universe, enumerating the characters by `G` gives a
four-leg tensor in the finite index universe of spectral placement prices. -/
theorem enumerated_fourier_rectanglePrice (P : SpectralPlacementPrices K Plane)
    (hP : FourierPlaneLaws P) (h : Admissible G K) (e : G ≃ Character G K)
    {L W : ℝ} (hL : 0 ≤ L) :
    rectanglePrice (fourierPhasePrice P) ((fourierMatrix G K).submatrix e id) L W =
      (L + Real.sqrt (L^2 + W^2)) * Real.logb 2 (Fintype.card G) := by
  let M := (fourierMatrix G K).submatrix e id
  have hM : M ≠ 0 := by
    intro hz
    have he := congrFun (congrFun hz (e.symm 1)) 0
    simp [M, fourierMatrix] at he
  apply rectanglePrice_eq_of_twoPhases P hM
    (twoPhases_characterTable_weightedSwap h.1 (card_character G K h) e) hP.sublinear
    (phaseCommonLabel_le P hP.flat M rfl)
    (fun w p r _ _ ↦ copiedSwap_price_le P (planeCopying_of_spectralPrices P) (fun j ↦ (w j : K)) p r)
    (fourierPhasePrice_longMove (planeCopying_of_spectralPrices P) M) hL

variable {F : Type} [Field F]

/-- The spectral rectangle price of the full character table, given the
planar spectral data. It equals the common-label bound at every aspect ratio. -/
theorem fourier_rectanglePrice (P : SpectralPlacementPrices F Plane) (hP : FourierPlaneLaws P)
    (h : Admissible G F) {L W : ℝ} (hL : 0 ≤ L) :
    rectanglePrice (fourierPhasePrice P) (fourierMatrix G F) L W =
      (L + Real.sqrt (L^2 + W^2)) * Real.logb 2 (Fintype.card G) := by
  let e := Fintype.equivOfCardEq (card_character G F h).symm
  change fourierPhasePrice P (fourierMatrix G F) _ = _
  rw [← fourierPhasePrice_reindex P _ (fourierMatrix G F) e (Equiv.refl G)]
  exact enumerated_fourier_rectanglePrice P hP h e hL

/-- The exact spectral value used at the thin rectangle in the lower bound. -/
theorem fourier_rectangleValue (P : SpectralPlacementPrices F Plane) (hP : FourierPlaneLaws P)
    (h : Admissible G F) {s c : ℝ} (hs : 0 ≤ s) (hu : c^2+s^2=1) :
    rectangleValue (fourierPhasePrice P) (fourierMatrix G F) s c =
      (2:ℝ) ^ ((2+2*s)*Real.logb 2 (Fintype.card G)/(2*(c+s))) :=
  normalized_rectangle_saturation (fourierMatrix_ne_zero G F) hu
    (fourier_rectanglePrice P hP h (mul_nonneg (by norm_num) hs))

end

end

end FiniteFourier
end LinearAlgebra
end OAI

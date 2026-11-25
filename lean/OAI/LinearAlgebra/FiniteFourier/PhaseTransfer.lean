import OAI.LinearAlgebra.FiniteFourier.Transfer
import OAI.LinearAlgebra.FiniteFourier.RectangularTensorValue
import OAI.LinearAlgebra.FiniteFourier.PhaseRegroup
import OAI.LinearAlgebra.FiniteFourier.PhaseSublevels
import OAI.LinearAlgebra.FiniteFourier.ForceSupport

/-! # The value of a small binary feedback computation at a thin rectangle -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

noncomputable section
section

variable {O I : Type} [Fintype O] [Fintype I]

/-- The small-computation bound for an actual normalized spectral rectangle value. Inputs from
planar geometry are the rectangle normalization, joint sublinearity, and the two common-label
diagonal bound. The proof uses the same normalized point at every tensor power. -/
theorem Feedback.rectangleValue_le {K : Type*} [Field K] [Infinite K] {s : ℕ}
    (F : Feedback K I O s) (hF : F.Regular) (P : SpectralPlacementPrices K Plane)
    (sublinear : ∀ (R C : Type) [Fintype R] [Fintype C] (M : Matrix R C K),
      SublinearPrice (fourierPhasePrice P M))
    {m u : ℝ} (hm : Real.logb 2 (Fintype.card O) = m) (hu : 1 ≤ u) (hbig : 48*u ≤ m)
    (hn : 0 < Fintype.card O)
    (budget : 2 * (s : ℝ) / thinBlock m u ≤ thinRankFraction u * Fintype.card O)
    (normal : P.price (Raw.diagonal (Fin 4) K (Fin 2)) (rectangleSites (2*thinS m u) (2*thinC m u)) =
      2*(thinC m u + thinS m u))
    (common : ∀ (M : Matrix O I K) (x : Fin 4 → Plane), fourierPhasePrice P M x ≤ m/2 *
      (dist (x 0) (x 2) + ‖x 0‖ + ‖x 2‖ + dist (x 1) (x 3) + ‖x 1‖ + ‖x 3‖)) :
    rectangleValue (fourierPhasePrice P) F.matrix (thinS m u) (thinC m u) ≤
      5*(2 : ℝ)^(-u)*thinFourierValue m u := by
  let h := thinBounds hu hbig
  have hc : 0 < thinC m u := by linarith only [h.c_half]
  obtain ⟨ν, powers, one⟩ := exists_rectangular_tensorValue P O I h.s_pos hc normal
  rw [← one]
  have hcard : (2 : ℝ)^m = Fintype.card O := by
    rw [← hm, Real.rpow_logb (by norm_num) (by norm_num) (Nat.cast_pos.mpr hn)]
  apply F.value_le_of_walk_and_rank hF h (by rwa [hcard]) ν
  · apply F.weighted_walk_of_rectangle_rows hm hu h ν _ powers
    · exact fun _ M ↦ (sublinear _ _ M).add_le
    · intro j M hM
      rw [fourierPhasePrice_height_zero P M (by positivity)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast rank_pos_of_matrix_ne_zero hM)
      exact_mod_cast M.rank_le_card_height
    · exact fun _ M _ ↦ fourierPhasePrice_width_zero P M (by linarith only [h.s_pos])
  · intro M hrank
    rw [one]
    apply rectangleValue_le_thinJ_of_rank hu h _ _ hrank (sublinear O I M).add_le (common M)
    intro _
    simpa using fourierPhasePrice_height_zero P M (show (0 : ℝ) ≤ 1 by norm_num)

/-- Small-price estimate for all matrices in the joint geometric border of regular systems. -/
theorem GeometricBorderAtMost.rectangleValue_le {K : Type*} [Field K] {S : ℕ} {M : Matrix O I K}
    (hb : GeometricBorderAtMost M S) (P : SpectralPlacementPrices (AlgebraicClosure K) Plane)
    (sublinear : ∀ (R C : Type) [Fintype R] [Fintype C] (A : Matrix R C (AlgebraicClosure K)),
      SublinearPrice (fourierPhasePrice P A))
    {m u : ℝ} (hm : Real.logb 2 (Fintype.card O) = m) (hu : 1 ≤ u) (hbig : 48*u ≤ m)
    (hn : 0 < Fintype.card O)
    (budget : 2 * (S : ℝ) / thinBlock m u ≤ thinRankFraction u * Fintype.card O)
    (normal : P.price (Raw.diagonal (Fin 4) (AlgebraicClosure K) (Fin 2))
      (rectangleSites (2*thinS m u) (2*thinC m u)) = 2*(thinC m u + thinS m u))
    (common : ∀ (A : Matrix O I (AlgebraicClosure K)) (x : Fin 4 → Plane),
      fourierPhasePrice P A x ≤ m/2 *
      (dist (x 0) (x 2) + ‖x 0‖ + ‖x 2‖ + dist (x 1) (x 3) + ‖x 1‖ + ‖x 3‖)) :
    rectangleValue (fourierPhasePrice P) (M.map (algebraMap K _)) (thinS m u) (thinC m u) ≤
      5*(2 : ℝ)^(-u)*thinFourierValue m u := by
  have h := thinBounds hu hbig
  apply hb.value_le _ (rectangleValue_sublevel_polynomials P _ _ _
    (by linarith only [h.s_pos, h.c_half]))
  rintro A ⟨s, hs, F, hF, rfl⟩
  exact F.rectangleValue_le hF P sublinear hm hu hbig hn ((by gcongr :
    2 * (s : ℝ) / thinBlock m u ≤ 2 * S / thinBlock m u).trans budget) normal common

end

end

end FiniteFourier
end LinearAlgebra
end OAI

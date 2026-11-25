import OAI.LinearAlgebra.FiniteFourier.Geometry
import OAI.LinearAlgebra.SpectralBooks.SpectralSpace

/-! # Single-leg and grouped bounds for phase placements

Transporting one tensor leg from a collapsed placement costs at most its
distance times the base-two logarithm of the leg dimension. For a controlled
phase with a repeated site, choosing that site as the common center reduces
the two triangle bounds to a single semiperimeter.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks

variable {E K : Type*} [NormedAddCommGroup E] [Field K]

/-- The actual one-leg transport estimate, for any finite tensor format. -/
theorem spectralPrice_single_le {I : Type} [Fintype I] [DecidableEq I]
    (P : SpectralPlacementPrices K E) (T : SiteTensor.Raw.{0} I K)
    (i : I) (v : E) :
    P.price T (Pi.single i v) ≤ Real.logb 2 (Fintype.card (T.Leg i)) * ‖v‖ := by
  have h := P.transport T (Pi.single i v) (fun _ ↦ 0)
  rw [P.collapsed, Real.dist_0_eq_abs] at h
  refine (le_abs_self _).trans (h.trans_eq ?_)
  rw [Finset.sum_eq_single i]
  · simp [mul_comm]
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- A common upper bound on log leg dimensions gives the one-leg hypothesis
in the first-phase force estimate. -/
theorem spectralPrice_single_le_of_logCard_le {I : Type} [Fintype I] [DecidableEq I]
    (P : SpectralPlacementPrices K E) (T : SiteTensor.Raw.{0} I K) {m : ℝ}
    (hdim : ∀ i, Real.logb 2 (Fintype.card (T.Leg i)) ≤ m) (i : I) (v : E) :
    P.price T (Pi.single i v) ≤ m * ‖v‖ :=
  (spectralPrice_single_le P T i v).trans
    (mul_le_mul_of_nonneg_right (hdim i) (norm_nonneg _))

/-- Subadditivity and the collapsed placement law allow the common-label
upper bound at the origin to be used at any center. -/
theorem common_labels_le_at_center {P : (Fin 4 → E) → ℝ} {m : ℝ}
    (hadd : ∀ x y, P (x + y) ≤ P x + P y)
    (hcollapse : ∀ U, P (fun _ ↦ U) = 0)
    (hcommon : ∀ x, P x ≤ m / 2 *
      (dist (x 0) (x 2) + ‖x 0‖ + ‖x 2‖ + dist (x 1) (x 3) + ‖x 1‖ + ‖x 3‖))
    (x : Fin 4 → E) (U : E) :
    P x ≤ m / 2 * (dist (x 0) (x 2) + dist (x 0) U + dist (x 2) U +
      dist (x 1) (x 3) + dist (x 1) U + dist (x 3) U) := by
  let c : Fin 4 → E := fun _ ↦ U
  have h := hadd (x - c) c
  rw [sub_add_cancel, show P c = 0 from hcollapse U, add_zero] at h
  simpa [c, dist_eq_norm, sub_sub_sub_cancel_right] using h.trans (hcommon (x - c))

/-- In either three-site grouping the triangle on the collapsed pair has
zero perimeter. The two bounds are ordered as in the first-phase argument. -/
theorem grouped_phase_semiperimeters {P : (Fin 4 → E) → ℝ} {m : ℝ}
    (hcommon : ∀ x (U : E), P x ≤ m / 2 *
      (dist (x 0) (x 2) + dist (x 0) U + dist (x 2) U +
        dist (x 1) (x 3) + dist (x 1) U + dist (x 3) U)) :
    (∀ A U A' : E, P ![A,U,A',U] ≤ m / 2 * (‖A-A'‖ + ‖A'-U‖ + ‖U-A‖)) ∧
    (∀ B U B' : E, P ![U,B,U,B'] ≤ m / 2 * (‖B'-B‖ + ‖B-U‖ + ‖U-B'‖)) := by
  constructor
  · intro A U A'
    simpa [dist_eq_norm, norm_sub_rev U A, add_comm, add_left_comm, add_assoc] using
      hcommon ![A,U,A',U] U
  · intro B U B'
    simpa [dist_eq_norm, norm_sub_rev B' B, norm_sub_rev U B', add_comm, add_left_comm, add_assoc] using
      hcommon ![U,B,U,B'] U

end FiniteFourier
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.FiniteFourier.FirstPhase
import OAI.LinearAlgebra.FiniteFourier.PhaseContraction
import OAI.LinearAlgebra.FiniteFourier.PhaseTriangleBounds
import OAI.LinearAlgebra.FiniteFourier.SwapReweight

/-! # Rectangle saturation for the finite abelian character table

The weighted swap supplied by the two character-table phases fixes their
boundary forces. The copying bounds allow the two input labels of the first
phase to move independently. Together these give the exact rectangle price.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical RealInnerProductSpace

variable {G : Type} {K : Type*} [Field K] [Fintype G] [Nonempty G]

/-- The rank and support endpoints, the network contraction and the weighted
swap all use the same actual field tensor price. The hypotheses here are the
two copying estimates and the planar sublinearity and common-label bounds. -/
theorem rectanglePrice_eq_of_twoPhases (P : SpectralPlacementPrices K Plane)
    {M : Matrix G G K} (hM : M ≠ 0) (hph : TwoPhasesGiveWeightedSwap M)
    (hsub : ∀ T : Raw.{0} (Fin 4) K, SublinearPrice (P.price T))
    (hcommon : ∀ x : Fin 4 → Plane, fourierPhasePrice P M x ≤
      Real.logb 2 (Fintype.card G)/2 *
        (dist (x 0) (x 2) + ‖x 0‖ + ‖x 2‖ + dist (x 1) (x 3) + ‖x 1‖ + ‖x 3‖))
    (hcopySwap : ∀ (w : G × G → Kˣ) (p r : Plane), ‖p‖ = 1 → ‖r‖ = 1 →
      P.price (copiedSwapRaw fun j ↦ (w j : K)) (fun j ↦ j.elim 0 (![p,r,-r,-p] : Fin 4 → Plane))
        ≤ P.price (swapRaw fun j ↦ (w j : K)) ![p,r,-r,-p])
    (hmove : ∀ A B A' B' x y : Plane, fourierPhasePrice P M ![x,y,A',B'] ≤
      fourierPhasePrice P M ![A,B,A',B'] + Real.logb 2 (Fintype.card G)/2 *
      (‖x-A‖ + ‖x-A'‖ - ‖A-A'‖ + ‖y-B‖ + ‖y-B'‖ - ‖B-B'‖))
    {L W : ℝ} (hL : 0 ≤ L) :
    rectanglePrice (fourierPhasePrice P) M L W =
      (L + Real.sqrt (L^2 + W^2)) * Real.logb 2 (Fintype.card G) := by
  let m := Real.logb 2 (Fintype.card G)
  let H := fourierPhasePrice P M
  have dims (i : Fin 4) : Fintype.card (phaseLeg G G i) = Fintype.card G := by
    fin_cases i <;> rfl
  have hu := rectanglePrice_le_of_common_labels (W := W) hL hcommon
  have hm : 0 ≤ m := Real.logb_nonneg (by norm_num) (by exact_mod_cast Fintype.card_pos (α := G))
  rcases hm.eq_or_lt with hzero | hpos
  · have h := P.transport (phaseRaw M) (rectangleSites L W) (fun _ ↦ 0)
    rw [P.collapsed] at h
    change dist (rectanglePrice (fourierPhasePrice P) M L W) 0 ≤
      ∑ i, dist _ _ * Real.logb 2 (Fintype.card (phaseLeg G G i)) at h
    simp only [dims, ← show (0:ℝ) = Real.logb 2 (Fintype.card G) from hzero,
      mul_zero, Finset.sum_const_zero] at h ⊢
    exact dist_le_zero.mp h
  obtain ⟨w, hnet⟩ := hph.exists_price_le P hM
  let S := swapRaw (fun j ↦ (w j : K))
  have hgroups := grouped_phase_semiperimeters
    (common_labels_le_at_center (hsub (phaseRaw M)).add_le (P.collapsed (phaseRaw M)) hcommon)
  have hforce (p r : Plane) (hp : ‖p‖ = 1) (hr : ‖r‖ = 1) :
      IsNormalizedForce m H ![p,r,-((1/2 : ℝ) • (p+r)),-((1/2 : ℝ) • (p+r))] := by
    apply exact_swap_first_phase_force hpos (hsub S) (hsub (phaseRaw M)) (hsub (phaseRaw M))
      (spectralPrice_single_le_of_logCard_le P S (fun i ↦ by
        change Real.logb 2 (Fintype.card (phaseLeg G G i)) ≤ m
        rw [dims])) hnet hgroups.1 hgroups.2 hp hr
    exact weightedSwap_diameter_lower P w hp hr (hcopySwap w p r hp hr)
  apply rectanglePrice_eq_of_four_legs hL hu
  intro x
  let xs : Fin 4 → Plane := ![x 0,x 1,x 2,x 3]
  have he : xs = x := by funext j; fin_cases j <;> rfl
  have hf := family_fourLeg_lowerBound m (fun _ : Unit ↦ H) (x 0) (x 1) (x 2) (x 3)
    (by simp) (by simpa only [ciSup_const] using hforce) (fun _ a b ↦ hmove _ _ _ _ a b)
  change _ ≤ ⨆ _ : Unit, H xs at hf
  simpa only [ciSup_const, he, dist_eq_norm] using hf

end

end FiniteFourier
end LinearAlgebra
end OAI

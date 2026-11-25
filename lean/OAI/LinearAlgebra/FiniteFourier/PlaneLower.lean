import OAI.LinearAlgebra.FiniteFourier.CharacterExtension
import OAI.LinearAlgebra.FiniteFourier.RadialPlaneLaws
import OAI.LinearAlgebra.FiniteFourier.PhaseTransfer
import OAI.LinearAlgebra.FiniteFourier.RectangleWidth
import OAI.LinearAlgebra.FiniteFourier.DenseLower
import OAI.LinearAlgebra.FiniteFourier.InverseBorder

/-!
# The Fourier lower bound from the spectral-plane theorem

For regular binary feedback circuits and their joint geometric border, the saturated character
table cannot have the value of a small computation. The same quantitative bound applies to the
inverse transform.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

variable {G : Type} [AddCommGroup G] [Fintype G] {K : Type*} [Field K]

/-- Proposition on small computations applied to Fourier and inverse Fourier matrices. `P` and
`hP` are precisely the spectral-plane inputs over the algebraic closure. -/
theorem fourier_border_lower_of_plane (P : SpectralPlacementPrices (AlgebraicClosure K) Plane)
    (hP : FourierPlaneLaws P) (hGK : Admissible G K) {S : ℕ}
    (hm : 144 ≤ Real.logb 2 (Fintype.card G))
    (hb : GeometricBorderAtMost (fourierMatrix G K) S ∨ GeometricBorderAtMost (inverseFourierMatrix G K) S) :
    (2 : ℝ)^(-(28 : ℝ)) * Fintype.card G * ⌊Real.sqrt (Real.logb 2 (Fintype.card G)) / 6⌋₊ < S := by
  let m := Real.logb 2 (Fintype.card G)
  have hpar := thinBounds (u := 3) (m := m) (by norm_num) (by linarith only [hm])
  have hN := Fintype.card_pos (α := G)
  let e₀ : G ≃ Character G K := Fintype.equivOfCardEq (card_character G K hGK).symm
  let f := algebraMap K (AlgebraicClosure K)
  let e := e₀.trans (characterExtensionEquiv hGK f)
  let M := (fourierMatrix G K).submatrix e₀ id
  have hM : GeometricBorderAtMost M S := by
    have h := hb.elim id ((geometricBorderAtMost_inverseFourierMatrix_iff G K hGK S).mp)
    exact h.reindex e₀.symm (Equiv.refl G)
  have baseChange : M.map f = (fourierMatrix G (AlgebraicClosure K)).submatrix e id := rfl
  have hnz : M.map f ≠ 0 := by
    intro h
    have hv := congrFun (congrFun h (e₀.symm 1)) 0
    simp [M, fourierMatrix, f] at hv
  have hunit : thinC m 3 ^ 2 + thinS m 3 ^ 2 = 1 := by
    rw [thinC, Real.sq_sqrt]
    · ring
    · nlinarith [hpar.s_le, hpar.s_pos]
  have hsat : rectangleValue (fourierPhasePrice P) (M.map f) (thinS m 3) (thinC m 3) =
      thinFourierValue m 3 := by
    apply normalized_rectangle_saturation hnz hunit
    rw [baseChange]
    apply enumerated_fourier_rectanglePrice P hP (hGK.map f) e
    exact mul_nonneg (by norm_num) hpar.s_pos.le
  apply fourier_lower_quantitative hm
  intro hsize
  rw [← hsat]
  nth_rewrite 2 [hsat]
  have hbig : 48 * (3 : ℝ) ≤ m := by dsimp only [m]; linarith only [hm]
  have hnorm : P.price (Raw.diagonal (Fin 4) (AlgebraicClosure K) (Fin 2))
      (rectangleSites (2*thinS m 3) (2*thinC m 3)) = 2*(thinC m 3 + thinS m 3) := by
    rw [rectangle_diagonal_price P hP.flat (by linarith only [hpar.s_pos]) (by linarith only [hpar.c_half])]
    ring
  exact hM.rectangleValue_le P (fun _ _ _ _ A ↦ hP.sublinear (phaseRaw A)) rfl
    (by norm_num) hbig hN hsize hnorm (fun A x ↦ phaseCommonLabel_le P hP.flat A rfl x)

/-- Joint convexity of prices on a spectral plane suffices, since the radial limit supplies the
common assignment required for copying, mean width and the transfer argument. -/
theorem fourier_border_lower_of_jointly_convex_plane (P : SpectralPlacementPrices (AlgebraicClosure K) Plane)
    (hc : ∀ {J : Type} [Fintype J] (T : Raw.{0} J (AlgebraicClosure K)), ConvexOn ℝ Set.univ (P.price T))
    (hGK : Admissible G K) {S : ℕ} (hm : 144 ≤ Real.logb 2 (Fintype.card G))
    (hb : GeometricBorderAtMost (fourierMatrix G K) S ∨ GeometricBorderAtMost (inverseFourierMatrix G K) S) :
    (2 : ℝ)^(-(28 : ℝ)) * Fintype.card G * ⌊Real.sqrt (Real.logb 2 (Fintype.card G)) / 6⌋₊ < S :=
  fourier_border_lower_of_plane _ (tangentPlane_fourierPlaneLaws P hc) hGK hm hb

/-- A uniform absolute lower bound valid at every order for which the Fourier theorem is stated.
The same constant works for all groups, fields, feedback systems and both directions. -/
theorem exists_fourier_border_sqrt_lower_of_plane : ∃ κ : ℝ, 0 < κ ∧
    ∀ (G : Type) [AddCommGroup G] [Fintype G] (K : Type*) [Field K],
      Admissible G K → 2 ≤ Fintype.card G → ∀ S : ℕ,
      (∃ P : SpectralPlacementPrices (AlgebraicClosure K) Plane, FourierPlaneLaws P) →
      (GeometricBorderAtMost (fourierMatrix G K) S ∨ GeometricBorderAtMost (inverseFourierMatrix G K) S) →
      κ * Fintype.card G * Real.sqrt (Real.logb 2 (Fintype.card G)) ≤ S := by
  obtain ⟨κ, hκ, h⟩ := uniform_fourier_sqrt_lower
  refine ⟨κ, hκ, fun G _ _ K _ had hn S ⟨P, hP⟩ hb ↦ ?_⟩
  have hlinear := fourier_border_card_le G K had hn S
  exact h _ _ hn (lt_of_lt_of_le (by omega) (hb.elim hlinear.1 hlinear.2))
    (fun hm ↦ fourier_border_lower_of_plane P hP had hm hb)

end FiniteFourier
end LinearAlgebra
end OAI

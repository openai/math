import OAI.Computability.BorderVNP.DiagonalPaidColumns
import OAI.LinearAlgebra.SpectralBooks.CompanionBorderSize
import OAI.LinearAlgebra.SpectralBooks.CompanionGeometry
import OAI.LinearAlgebra.SpectralBooks.CompanionProfileScalarExtension
import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.CompanionPstarGrid

/-! # Matrix multiplication over every field

A profiled shortening gives a paid identity after scalar extension. The companion
border-stretch theorem applies to its integral signed polynomial. The Hamiltonian-cycle
projection transfers this lower bound to the same subcubic grids that tree compression
evaluates. The resulting non-tree witness supplies the spectral plane and finite ranks.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Filter
open scoped BigOperators
universe u

/-- Stretch for the companion's integral signed polynomial, with one exponent for all
coefficient fields of the characteristic. Both bounds use its degree-`n` component. -/
theorem companion_signed_border_stretch (K : Type) [Field K] (p : ℕ) [CharP K p]
    {D : ℕ} (hD : 2 ≤ D) (short : Crossing.HasProfileShortening K D) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (F : Type u) [Field F] [CharP F p], ∀ᶠ n : ℕ in atTop,
      let f := MvPolynomial.map (Int.castRingHom F) (OAI.Computability.BorderVNP.Pstar n)
      (2 : ℝ) ^ ((n : ℝ) ^ ε) ≤ (OAI.Computability.BorderVNP.borderSize n f : ℝ) ∧
        DegreeBorderSizeAtLeast n ((2 : ℝ) ^ ((n : ℝ) ^ ε)) f := by
  obtain ⟨ε, pos, hard⟩ := OAI.Computability.BorderVNP.ProvedStretch.profile K p
    (CompanionBridge.companionProfile_algebraicClosure hD short)
  refine ⟨ε, pos, ?_⟩
  intro F _ _
  filter_upwards [hard] with n hn
  dsimp only
  refine ⟨?_, degreeBorderSizeAtLeast_intCast_of_companion p n _ _ hn⟩
  rw [OAI.Computability.BorderVNP.borderSize_intCast_eq (K := F) (F := AlgebraicClosure K) p,
    OAI.Computability.BorderVNP.borderSize_eq_groundBorderSize]
  exact hn

/-- Sharp's tree compression is incompatible with the companion's signed-polynomial
lower bound on the projected subcubic grids. -/
private theorem allFieldBounds (F : Type*) [Field F] :
    HasNonTreeWireMetric F ∧ RectangularRankBound F ∧ 3 / Real.sqrt 2 ≤ formalOmega F 1 1 1 ∧
      3 / Real.sqrt 2 ≤ divisionOmega F 1 1 1 := by
  obtain ⟨K, _, closed, hp⟩ := exists_algebraicallyClosed_reference
    (CharP.char_is_prime_or_zero F (ringChar F))
  let : IsAlgClosed K := closed
  let : CharP K (ringChar F) := hp
  have witness : HasNonTreeWireMetric K := by
    apply hasNonTreeWireMetric_of_profile_grid_stretch
    intro shortening
    obtain ⟨ε, pos, hard⟩ := companion_signed_border_stretch.{0} K (ringChar F) (D := 2) le_rfl shortening
    exact IndependentSetGraph.hardSubcubicGrids_of_companionPstar pos ((hard K).mono fun _ hn => hn.2)
  have heq : ringChar K = ringChar F := ringChar.eq_iff.mpr hp
  exact ⟨(hasNonTreeWireMetric_iff_of_ringChar_eq heq).mp witness,
    rank_and_exponent_of_nonTreeWireMetric witness F heq⟩

/-- The spectral wire metric has a non-tree witness over the original field. -/
theorem nonTreeWireMetric_every_field (F : Type*) [Field F] : HasNonTreeWireMetric F :=
  (allFieldBounds F).1

/-- A single spectral placement on the Euclidean plane makes every finite tensor price jointly convex. -/
theorem matrix_spectral_plane (F : Type*) [Field F] :
    ∃ P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 2)),
      ∀ {I : Type} [Fintype I] (T : SiteTensor.Raw.{0} I F), ConvexOn ℝ Set.univ (P.price T) :=
  exists_jointly_convex_spectral_plane (nonTreeWireMetric_every_field F)

/-- The flattening and radical inequalities for all three finite ranks in every positive format. -/
theorem matrix_rectangular_rank_bounds (F : Type*) [Field F] (x y z : ℕ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    let T := matrixTensor F x y z
    let m := loads (Real.logb 2 x) (Real.logb 2 y) (Real.logb 2 z)
    let test := fun L : ℝ => (∀ i, m i ≤ L) ∧ L ≤ ∑ i, Real.sqrt (L ^ 2 - m i ^ 2)
    test (Real.logb 2 (asymptoticRank T)) ∧ test (Real.logb 2 (geometricBorderRank T)) ∧
      test (Real.logb 2 (tensorRank T)) := by
  exact (allFieldBounds F).2.1 x y z hx hy hz

/-- The square formal arithmetic and division exponents over the original field. -/
theorem matrix_square_exponent (F : Type*) [Field F] :
    3 / Real.sqrt 2 ≤ formalOmega F 1 1 1 ∧ 3 / Real.sqrt 2 ≤ divisionOmega F 1 1 1 :=
  (allFieldBounds F).2.2

/-- In every characteristic the Gaussian estimates hold in every positive format, or
one positive exponent gives the eventual lower bound for the integral `Pstar` in every
field of the characteristic. -/
theorem matrix_characteristic_alternative (p : ℕ) :
    (∀ (F : Type u) [Field F] [CharP F p], GaussianMatrixTest F ∧
      2 * Real.exp (stdNormalQuantile (2 / 3) ^ 2 / 2) ≤ divisionOmega F 1 1 1) ∨
    ∃ ε : ℝ, 0 < ε ∧ ∀ (F : Type u) [Field F] [CharP F p], ∀ᶠ n : ℕ in atTop,
      let f := MvPolynomial.map (Int.castRingHom F) (OAI.Computability.BorderVNP.Pstar n)
      (2 : ℝ) ^ ((n : ℝ) ^ ε) ≤ (OAI.Computability.BorderVNP.borderSize n f : ℝ) ∧
        DegreeBorderSizeAtLeast n ((2 : ℝ) ^ ((n : ℝ) ^ ε)) f := by
  by_cases possible : p.Prime ∨ p = 0
  · obtain ⟨K, _, _, hp⟩ := exists_algebraicallyClosed_reference possible
    let : CharP K p := hp
    obtain gauss | ⟨D, hD, shortening⟩ := gaussianMatrixTest_or_profile_shortening K
    · left
      intro F _ _
      have h := (gaussianMatrixTest_iff_of_charP K F p).mp gauss
      exact ⟨h, by rw [divisionOmega_square_eq_formalOmega]; exact formalOmega_gaussian_square_lower_bound h⟩
    · exact Or.inr (companion_signed_border_stretch K p hD shortening)
  · left
    intro F _ _
    exact (possible (CharP.char_is_prime_or_zero F p)).elim

end SpectralBooks
end LinearAlgebra
end OAI

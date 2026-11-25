import OAI.LinearAlgebra.SpectralBooks.SquareExponent
import OAI.LinearAlgebra.SpectralBooks.StudentTestFromFlat
import OAI.ThreeFlat.StudentProfile
import OAI.ThreeFlat.RationalBound
import OAI.ThreeFlat.FiniteFieldReduction

namespace OAI
/-! # The square exponent from the dimension-three Student inequality

The finite test at order two suffices because the base-two logarithm of the
asymptotic rank in that format is the square arithmetic exponent.
-/

namespace ThreeFlat

open LinearAlgebra.SpectralBooks

/-- The square specialization of the three-dimensional finite rank test. -/
theorem square_exponents_of_studentMatrixTest {F : Type*} [Field F]
    (h : StudentMatrixTest F 3) :
    omegaThree ≤ formalOmega F 1 1 1 ∧ omegaThree ≤ divisionOmega F 1 1 1 := by
  have hs := h 2 2 2 (by decide) (by decide) (by decide)
  rw [square_asymptoticRank_eq_rpow_formalOmega F (by decide), Nat.cast_ofNat,
    Real.logb_rpow (by norm_num) (by norm_num), Real.logb_self_eq_one (by norm_num),
    unit_weight_loads] at hs
  have hL : 2 ≤ formalOmega F 1 1 1 := by
    simpa only [unit_weight_loads] using
      load_le_formalOmega F (w12 := 1) (w23 := 1) (w31 := 1)
        zero_le_one zero_le_one zero_le_one 0
  have hω := omegaThree_le_of_profile hL
    (profile_le_oneThird_of_studentBound (by norm_num : (0 : ℝ) < 2) hL hs)
  exact ⟨hω, (divisionOmega_square_eq_formalOmega F).symm ▸ hω⟩

/-- A three-flat over one reference field gives the square inequalities in
both arithmetic models over every field of the same characteristic. -/
theorem square_exponents_of_reference_threeFlat (K : Type) [Field K] (F : Type*) [Field F]
    (hchar : ringChar K = ringChar F)
    (flat : Nonempty (SpectralPlacementPrices K (EuclideanSpace ℝ (Fin 3)))) :
    omegaThree ≤ formalOmega F 1 1 1 ∧ omegaThree ≤ divisionOmega F 1 1 1 := by
  have h := studentMatrixTest_of_spectral_flat K (fun _ _ _ Q hg => Q.catZero hg)
    (by decide : 2 ≤ 3) flat
  apply square_exponents_of_studentMatrixTest
  intro x y z hx hy hz
  rw [← asymptoticRank_matrixTensor_eq_of_ringChar_eq K F hchar]
  exact h x y z hx hy hz

/-- For the all-field conclusion it suffices to construct the placements in
positive prime characteristic. This also covers characteristic zero by
specializing finite tensor-rank witnesses. -/
theorem square_exponents_of_prime_threeFlats
    (flat : ∀ (p : ℕ) [Fact p.Prime],
      Nonempty (SpectralPlacementPrices (ZMod p) (EuclideanSpace ℝ (Fin 3))))
    (F : Type*) [Field F] :
    omegaThree ≤ formalOmega F 1 1 1 ∧ omegaThree ≤ divisionOmega F 1 1 1 := by
  have h := square_exponent_lower_bound_of_prime_fields (c := omegaThree)
    (fun p _ => (square_exponents_of_reference_threeFlat (ZMod p) (ZMod p) rfl (flat p)).1) F
  exact ⟨h, (divisionOmega_square_eq_formalOmega F).symm ▸ h⟩

/-- A violation of the square bound forces an actual finite width shortening
of the three-axis crossing on the reference field. -/
theorem shortened_crossing_of_square_violation (K : Type) [Field K] (F : Type*) [Field F]
    (hchar : ringChar K = ringChar F) (hω : divisionOmega F 1 1 1 < omegaThree) :
    ∃ m : ℕ, 0 < m ∧ Crossing.ShortenedCrossing K 3 m := by
  apply shortenedCrossing_of_no_flat K (by decide : 2 ≤ 3)
    (hasSpectralAxisExtensions_of_curvature K (fun _ _ _ Q hg => Q.catZero hg) 3)
  exact fun flat => hω.not_ge (square_exponents_of_reference_threeFlat K F hchar flat).2

end ThreeFlat

end OAI

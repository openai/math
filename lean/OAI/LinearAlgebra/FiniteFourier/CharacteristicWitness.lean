import OAI.LinearAlgebra.FiniteFourier.SmallGroupLower
import OAI.LinearAlgebra.SpectralBooks.WireMetricBaseChange

/-! # The Fourier lower bound from the characteristic-wise non-tree theorem

A finite witness in just one field of each characteristic suffices for the
same geometric-feedback lower bound over every admissible field.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks

universe u v

/-- The explicit lower constant works for every field in a characteristic
admitting a finite non-tree witness. It is independent of the witness.
The dense-matrix estimate covers orders below the quantitative threshold. -/
theorem fourierBorderLower_of_characteristic_witness {F : Type*} [Field F]
    (hw : HasNonTreeWireMetric F) (G : Type u) (K : Type v)
    [AddCommGroup G] [Fintype G] [Field K] (hc : ringChar F = ringChar K)
    (had : Admissible G K) (hn : 2 ≤ Fintype.card G) (S : ℕ)
    (hb : GeometricBorderAtMost (fourierMatrix G K) S ∨
      GeometricBorderAtMost (inverseFourierMatrix G K) S) :
    1 / (12 * 2 ^ 28 : ℝ) * Fintype.card G * Real.sqrt (Real.logb 2 (Fintype.card G)) ≤ S := by
  by_cases hm : 144 ≤ Real.logb 2 (Fintype.card G)
  · have he := hc.trans (Algebra.ringChar_eq K (AlgebraicClosure K))
    obtain ⟨P, hP⟩ := exists_jointly_convex_spectral_plane
      ((hasNonTreeWireMetric_iff_of_ringChar_eq he).mp hw)
    exact (fourier_sqrt_lower_of_quantitative hm
      (fourier_border_lower_of_plane_any_universe (tangentPlane P) (tangentPlane_fourierPlaneLaws P hP)
        had hm hb)).le
  · obtain ⟨hf, hi⟩ := fourier_border_card_le G K had hn S
    have hN : (Fintype.card G : ℝ) ≤ S := by exact_mod_cast hb.elim hf hi
    have hs : Real.sqrt (Real.logb 2 (Fintype.card G)) ≤ 12 := by
      exact Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
    calc
      _ ≤ 1 / (12 * 2 ^ 28 : ℝ) * Fintype.card G * 12 :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ (Fintype.card G : ℝ) := by nlinarith only [Nat.cast_nonneg (α := ℝ) (Fintype.card G)]
      _ ≤ S := hN

/-- The algebraic closures in the geometric border can vary in both
cardinality and characteristic. A single finite witness per characteristic
gives an absolute lower constant for all of them. -/
theorem uniformFourierBorderLower_of_characteristic_witnesses
    (witness : ∀ p : ℕ, p.Prime ∨ p = 0 → ∃ (F : Type) (_ : Field F),
      ringChar F = p ∧ HasNonTreeWireMetric F) : UniformFourierBorderLower.{u,v} := by
  refine ⟨1 / (12 * 2 ^ 28), by positivity, ?_⟩
  intro G K _ _ _ had hn S hb
  obtain ⟨F, _, hc, hw⟩ := witness (ringChar K) (CharP.char_is_prime_or_zero K (ringChar K))
  exact fourierBorderLower_of_characteristic_witness hw G K hc had hn S (Or.inl hb)

end FiniteFourier
end LinearAlgebra
end OAI

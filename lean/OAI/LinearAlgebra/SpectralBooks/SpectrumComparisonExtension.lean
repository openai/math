import OAI.LinearAlgebra.SpectralBooks.Spectrum
import OAI.LinearAlgebra.SpectralBooks.PolynomialOverhead

/-! # Restricting strict spectral comparisons along a semiring homomorphism -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped NNReal

/-- Strict comparison by all spectral points of the target implies weak comparison by
every normalized source point monotone for the induced preorder, provided the target
admits comparison of positive powers up to a fixed natural multiple. -/
theorem le_of_strict_restricted_spectral_comparison
    {S T : Type*} [CommSemiring S] [CommSemiring T] [Preorder T]
    (i : S →+* T) (f : S →+* ℝ≥0)
    (hmono : ∀ x y, i x ≤ i y → f x ≤ f y)
    (hcompare : ∀ (x y : T), x ≠ 0 → y ≠ 0 →
      (∀ g : normalizedSpectrum ((· ≤ ·) : T → T → Prop), g.val x < g.val y) →
      ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → x ^ n ≤ C • y ^ n)
    (x y : S)
    (gap : ∀ g : normalizedSpectrum ((· ≤ ·) : T → T → Prop), g.val (i x) < g.val (i y)) :
    f x ≤ f y := by
  have hne (z : S) : i (z + 1) ≠ 0 := by
    intro hz
    have hle := hmono (z + 1) 0 (by simp [hz])
    simp at hle
  obtain ⟨C, _, hC⟩ := hcompare (i (x + 1)) (i (y + 1)) (hne x) (hne y) (by
    intro g
    simp only [map_add, map_one, g.2.2.2.1]
    exact add_lt_add_left (gap g) _)
  have hle : f (x + 1) ≤ f (y + 1) := by
    apply nnreal_le_of_pow_le_polynomial_mul_pow C
    intro m hm
    have hp := hmono ((x + 1) ^ m) (C • (y + 1) ^ m) (by simpa using hC m hm)
    simp only [map_pow, nsmul_eq_mul, map_mul, map_natCast] at hp
    apply hp.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hnat : C ≤ (m + 1) ^ C :=
      (Nat.lt_two_pow_self (n := C)).le.trans (Nat.pow_le_pow_left (by omega) _)
    exact_mod_cast hnat
  simpa using hle

end SpectralBooks
end LinearAlgebra
end OAI

import OAI.Computability.VPVNP.SpectralCompactGap
import OAI.Computability.VPVNP.SpectralStateHom
import OAI.Computability.VPVNP.SpectralCatalyst

/-!
# Uniform comparison of powers from spectral separation

A strict inequality at every point of the compact spectrum gives an integer
margin. Detecting this stronger inequality in the rational order cone, clearing
denominators, and removing additive slack gives a restriction with a single
number of copies for all powers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Spectral

variable {S : Type*} [CommSemiring S] [Preorder S] [NoZeroDivisors S] [Nontrivial S]

/-- Lemma 2.1 in the ordered-semiring setting of Appendix A.1. A monotone
natural-valued rank is a witness that the negative unit is outside the
localized order cone. Strict comparison at every spectral point gives the
same finite copy bound for all powers. -/
theorem strict_spectral_comparison [CharZero S] (H : OrderBounds S)
    (rank : S →+* ℕ) (hmono : Monotone rank)
    {x y : S} (hy : y ≠ 0)
    (h : ∀ F : S →+* ℝ, Monotone F → F x < F y) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ m : ℕ, x ^ m ≤ (K : S) * y ^ m := by
  have hs : ∀ F ∈ spectrumValues S, F x < F y := by
    rintro _ ⟨F, hF, rfl⟩
    exact h F hF
  obtain ⟨b, hb⟩ := compact_strict_comparison_margin (spectrumValues_isCompact H) hs
  have hm : ∀ F : S →+* ℝ, Monotone F →
      F (((b : S) + 1) * x) < F ((b : S) * y) := by
    intro F hF
    simpa only [map_add, map_mul, map_one, map_natCast] using hb F ⟨F, hF, rfl⟩
  obtain ⟨c, hc, w, hw⟩ := clear_comparison H (fractionPositive_of_spectrum_lt H rank hmono _ _ hm)
  obtain ⟨D, hD, htrade⟩ := remove_additive_slack H hc hy b hw
  exact catalyst_uniform_bound H hD htrade

end Spectral

end VPVNP
end Computability
end OAI

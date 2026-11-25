import OAI.LinearAlgebra.FiniteFourier.RadixButterfly
import OAI.LinearAlgebra.FiniteFourier.ToeplitzAdditiveWord
import OAI.LinearAlgebra.FiniteFourier.AtTwoFourierInverse

/-! # Rectangular Toeplitz additions over the protected rings

Both radix choices use two occupied cyclic arrays. All coefficients of the
word lie in the same ring as the supplied Fourier root and Toeplitz entries.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {R : Type*} [CommRing R] {r a e : ℕ}

/-- The dyadic and ternary short transforms each give an additive Toeplitz word
of depth linear in the radix exponent, restoring two length-`r^j` arrays. -/
theorem protected_rectangularToeplitz_word (hr : r = 2 ∨ r = 3) (j : ℕ)
    (hab : a + e ≤ r ^ j) (u : Rˣ) (hu : u ^ (r ^ j) = 1) (hb : IsUnit ((r ^ j : ℕ) : R))
    (hsep : Pairwise fun i k : Fin (r ^ j) ↦ IsUnit ((u : R)^i.val - (u : R)^k.val))
    (hs : ∀ s : R, ∃ t : R, IsUnit t ∧ IsUnit (s-t)) (c : ℤ → R) :
    AdditiveWord (Fin (r^j) ⊕ (Fin (r^j) ⊕ (Empty ⊕ Empty))) (104*j+46)
      (rectangularToeplitz a e c) := by
  have hr0 : r ≠ 0 := by rcases hr with rfl | rfl <;> decide
  let : NeZero (r^j) := ⟨pow_ne_zero j hr0⟩
  have hpow : (u : R)^(r^j) = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  have hF := (layerWord_smallRadixPow_of_separated hr j hpow hsep).occupied (W := Empty)
  have hU := occupiedWord_inverse_geometricMatrix_of_separated u hu hb hsep hF
  have h := additiveWord_rectangularToeplitz_of_inverse hab hpow
    (inverse_geometricMatrix_mul_of_separated u hu hb hsep) hs c hF hU
  convert h using 1
  omega

end FiniteFourier
end LinearAlgebra
end OAI

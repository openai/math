import OAI.LinearAlgebra.SpectralBooks.SignedWitness
import OAI.LinearAlgebra.SpectralBooks.BorderCharacteristic

/-! # The circuit-size bound throughout one characteristic

These results specialize the degree-component border model to the signed universal
polynomial. They transport a lower bound from one field to all fields of its
characteristic with the same exponent and the same threshold length.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

/-- In a fixed characteristic the signed witness has the same geometric border complexity
in each degree, independently of the coefficient field. -/
theorem signedWitnessBorderSize_eq_of_charP (F G : Type*) [Field F] [Field G] (p n : ℕ)
    [CharP F p] [CharP G p] :
    degreeBorderSize n (signedWitnessPolynomial F n) =
      degreeBorderSize n (signedWitnessPolynomial G n) := by
  simpa only [map_signedWitnessPolynomial] using
    (degreeBorderSize_eq_of_charP F G p n (signedWitnessPolynomial ℤ n))

/-- The degree-component stretched-exponential estimate over one field. -/
def SignedWitnessHardness (F : Type*) [Field F] (ε : ℝ) : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, DegreeBorderSizeAtLeast n ((2 : ℝ) ^ ((n : ℝ) ^ ε))
    (signedWitnessPolynomial F n)

/-- The field change preserves every single length that satisfies the lower bound. -/
theorem signedWitnessHardness_iff_of_charP (F G : Type*) [Field F] [Field G] (p : ℕ)
    [CharP F p] [CharP G p] (ε : ℝ) :
    SignedWitnessHardness F ε ↔ SignedWitnessHardness G ε :=
  Filter.eventually_congr (Filter.Eventually.of_forall fun n ↦ by
    unfold DegreeBorderSizeAtLeast
    rw [signedWitnessBorderSize_eq_of_charP F G p n])

end SpectralBooks
end LinearAlgebra
end OAI

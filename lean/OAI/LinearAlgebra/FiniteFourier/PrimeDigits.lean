import OAI.LinearAlgebra.FiniteFourier.Cyclic

/-! # Tensor powers of a fixed prime Fourier kernel

The order is the per-digit radix, and digit positions index the factors.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- The k-digit tensor power of the unnormalized positive-sign Fourier matrix
with primitive radix-ℓ root ζ. -/
def primeTransform {K : Type*} [CommSemiring K] (ℓ k : ℕ) (ζ : K) :
    Matrix (Fin k → Fin ℓ) (Fin k → Fin ℓ) K :=
  fun i j => ∏ d, ζ ^ ((i d).val * (j d).val)

@[simp] theorem primeTransform_apply {K : Type*} [CommSemiring K] (ℓ k : ℕ) (ζ : K)
    (i j : Fin k → Fin ℓ) : primeTransform ℓ k ζ i j = ∏ d, ζ ^ ((i d).val * (j d).val) :=
  rfl

theorem primeTransform_apply_dft {K : Type*} [CommSemiring K] (ℓ k : ℕ) (ζ : K)
    (i j : Fin k → Fin ℓ) : primeTransform ℓ k ζ i j = ∏ d, dftMatrix ℓ ζ (i d) (j d) := rfl

end FiniteFourier
end LinearAlgebra
end OAI

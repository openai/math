import OAI.LinearAlgebra.FiniteFourier.PrimeKernel
import OAI.LinearAlgebra.FiniteFourier.ExtensionCircuit

/-! # Descent after the prime Fourier recursion

The finite repair extension depends only on the fixed template. We run the
whole recursion there before restricting scalars. Thus the cost of expanding
an extension gate in a basis is paid once, and the strict saving of recursive
calls per independent row is preserved.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {R E : Type*} [CommSemiring R] [CommSemiring E]

theorem primeTransform_map (φ : R →+* E) (ℓ k : ℕ) (ζ : R) :
    (primeTransform ℓ k ζ).map φ = primeTransform ℓ k (φ ζ) := by
  ext i j
  simp [primeTransform]

/-- One constant works for every ground ring and every finite free repair
extension of rank at most `d` that realizes the given batch. -/
theorem uniform_primeTransform_bound_of_extension_batch {ℓ A W σ C d : ℕ} {θ : ℝ}
    (hℓ : 1 < ℓ) (hA : 0 < A) (hW : 0 < W) (hθ : 0 ≤ θ)
    (hs : (σ : ℝ) / W < (A : ℝ)^θ) :
    ∃ B > (0 : ℝ), ∀ (R E : Type*) [CommRing R] [CommRing E] [Algebra R E]
      (D : Type*) [Fintype D] (_ : Module.Basis D R E) (_ : D),
      Fintype.card D ≤ d → ∀ ζ : R, PrimeKernelBatch ℓ A W σ C (algebraMap R E ζ) →
        ∀ k : ℕ, (complexity (primeTransform ℓ k ζ) : ℝ) ≤
          B * (ℓ : ℝ)^k * (1 + (k : ℝ))^θ := by
  obtain ⟨B, hB, bound⟩ := uniform_primeTransform_bound_of_batch (C := C) hℓ hA hW hθ hs
  refine ⟨2 * (d : ℝ)^2 * B + d + 1, by positivity, ?_⟩
  intro R E _ _ _ D _ b d₀ hd ζ hb k
  have hbnd := bound E (algebraMap R E ζ) hb k
  have h := complexity_le_of_extensionBasis b d₀ (primeTransform ℓ k ζ)
  rw [primeTransform_map] at h
  simp only [Fintype.card_fun, Fintype.card_fin] at h
  have h' : (complexity (primeTransform ℓ k ζ) : ℝ) ≤
      2 * (d : ℝ)^2 * complexity (primeTransform ℓ k (algebraMap R E ζ)) + d * (ℓ : ℝ)^k := by
    exact_mod_cast h.trans (Nat.add_le_add (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hd 2))) (Nat.mul_le_mul_right _ hd))
  have hone : 1 ≤ (1 + (k : ℝ)) ^ θ :=
    Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) k]) hθ
  have he := mul_le_mul_of_nonneg_left hbnd (show 0 ≤ 2 * (d : ℝ)^2 by positivity)
  have hp := mul_le_mul_of_nonneg_left hone (show 0 ≤ (d : ℝ) * (ℓ : ℝ)^k by positivity)
  linarith only [h', he, hp,
    mul_nonneg (show 0 ≤ (ℓ : ℝ)^k by positivity) (zero_le_one.trans hone)]

end FiniteFourier
end LinearAlgebra
end OAI

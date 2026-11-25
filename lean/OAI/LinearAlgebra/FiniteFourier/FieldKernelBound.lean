import OAI.LinearAlgebra.FiniteFourier.TernaryDescent
import OAI.LinearAlgebra.FiniteFourier.PrimeShearDescent

/-! # Uniform prime Fourier bounds imply uniform shear bounds over fields -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

universe u

/-- At fixed radix and exponent the same constant bounds all tensor powers
of the Fourier kernel, uniformly in the admissible field and primitive root. -/
def UniformFieldKernelBound (ℓ : ℕ) (θ : ℝ) : Prop :=
  ∃ c > (0 : ℝ), ∀ (E : Type u) [Field E], (ℓ : E) ≠ 0 → ∀ ζ : E, IsPrimitiveRoot ζ ℓ →
    ∀ k : ℕ, (complexity (primeTransform ℓ k ζ) : ℝ) ≤ c * (ℓ : ℝ)^k * (1 + (k : ℝ))^θ

/-- A fixed batch size and strict saving suffice uniformly over the fields
in which the radix is invertible and the primitive root exists. -/
theorem uniformFieldKernelBound_of_batch {ℓ A W σ C : ℕ} {θ : ℝ}
    (hℓ : 1 < ℓ) (hA : 0 < A) (hW : 0 < W) (hθ : 0 ≤ θ) (hs : (σ : ℝ) / W < (A : ℝ)^θ)
    (hbatch : ∀ (E : Type u) [Field E], (ℓ : E) ≠ 0 → ∀ ζ : E, IsPrimitiveRoot ζ ℓ →
      PrimeKernelBatch ℓ A W σ C ζ) : UniformFieldKernelBound.{u} ℓ θ := by
  obtain ⟨c, hc, hpow⟩ := uniform_primeTransform_bound_of_batch (C := C) hℓ hA hW hθ hs
  exact ⟨c, hc, fun E _ hℓE ζ hζ => hpow E ζ (hbatch E hℓE ζ hζ)⟩

/-- The radix-two and radix-three Fourier bounds together suffice for all
fields. The two kernel constants may differ and both precede the ground field. -/
theorem uniform_shearTensorBound_of_fieldKernelBounds {θ : ℝ} (hθ : 0 ≤ θ)
    (hb : UniformFieldKernelBound.{u} 2 θ) (ht : UniformFieldKernelBound.{u} 3 θ) :
    ∃ D > (0 : ℝ), ∀ (K : Type u) [Field K], ShearTensorBound K θ D := by
  obtain ⟨b, hbpos, hbinary⟩ := hb
  obtain ⟨t, htpos, hternary⟩ := ht
  let B := 512*b + 8
  let T := 2 * 9^2 * (8 * 28 * t) + 9
  refine ⟨max B T, lt_of_lt_of_le (by dsimp [B]; positivity : 0 < B) (le_max_left B T), fun K _ j => ?_⟩
  by_cases h2 : (2 : K) = 0
  · have h := charTwo_shearTensorBound_of_kernel htpos hθ (fun E _ hz ζ hζ k => by
      have h3 : (3 : E) ≠ 0 := by rw [show (3 : E) = 2+1 by norm_num, hz, zero_add]; exact one_ne_zero
      simpa using hternary E (by simpa using h3) ζ hζ k) K h2 j
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right B T)
      (by positivity)) (by positivity))
  · let E := CyclotomicField 8 K
    have h2E : (2 : E) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero (algebraMap K E)).mpr h2
    have hchar : ringChar E ≠ 2 := by
      intro he
      exact h2E (by simpa [he] using CharP.cast_eq_zero E (ringChar E))
    have hζ : IsPrimitiveRoot (-1 : E) 2 := IsPrimitiveRoot.neg_one (ringChar E) hchar
    have hc := hbinary E (by simpa using h2E) (-1) hζ j
    have hd : (complexity (gridTensor (fun _ : Fin j => unitShear K)) : ℝ) ≤
        512 * (complexity (primeTransform 2 j (-1 : E)) : ℝ) + 8 * (2 : ℝ)^j := by
      exact_mod_cast complexity_shear_le_binary_extension K h2 j
    have hone : 1 ≤ (1 + (j : ℝ))^θ :=
      Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) j]) hθ
    have h : (complexity (gridTensor (fun _ : Fin j => unitShear K)) : ℝ) ≤
        B * (2 : ℝ)^j * (1 + (j : ℝ))^θ := by
      dsimp [B]
      push_cast at hc
      nlinarith only [hd, hc, mul_le_mul_of_nonneg_left hone (show 0 ≤ (2 : ℝ)^j by positivity)]
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left B T)
      (by positivity)) (by positivity))

end FiniteFourier
end LinearAlgebra
end OAI

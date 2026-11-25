import OAI.Computability.NearSquareRoot.SynchronizedCirculant
import OAI.Computability.NearSquareRoot.SynchronizedPaddedChirp
import OAI.Computability.NearSquareRoot.SynchronizedChirpBound

/-! # Fourier multipliers of the padded Bluestein convolution

Each signed offset contributes to exactly one cyclic bin. Reduction modulo the
padded length leaves its phase unchanged at each integer Fourier frequency.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Finset Matrix

private theorem phase_chirp (x : ℝ) : phase x = Chirp.phase x := by
  unfold phase Chirp.phase
  push_cast
  congr 1
  ring

private theorem phase_emod_ratio {r : ℕ} [NeZero r] (j : ℕ) (h : ℤ) :
    phase ((j : ℝ) * ((h % (r : ℤ) : ℤ) : ℝ) / r) =
      phase ((j : ℝ) / r * h) := by
  have hr : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  rw [show (j : ℝ) * ((h % (r : ℤ) : ℤ) : ℝ) / r =
          (j : ℝ) / r * h - (((j : ℤ) * (h / r) : ℤ) : ℝ) by
        rw [Int.emod_def]
        push_cast
        field_simp, phase_sub, phase_int, div_one]

/-- Folding finitely many signed samples into residues commutes with summing
against a discrete cyclic character. Collisions of signed offsets are permitted. -/
theorem folded_spectrum {r : ℕ} [NeZero r] (s : Finset ℤ) (v : ℤ → ℂ) (ξ : Fin r) :
    (∑ t : Fin r, (∑ h ∈ s, if h % (r : ℤ) = (t.val : ℤ) then v h else 0) *
          phase ((ξ.val : ℝ) * t.val / r)) =
      ∑ h ∈ s, v h * phase ((ξ.val : ℝ) / r * h) := by
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun h _ => ?_
  have hr : 0 < (r : ℤ) := by exact_mod_cast NeZero.pos r
  have h₀ := Int.emod_nonneg h hr.ne'
  have h₁ := Int.emod_lt_of_pos h hr
  let t : Fin r := ⟨(h % (r : ℤ)).toNat, by omega⟩
  have ht : (t.val : ℤ) = h % r := Int.toNat_of_nonneg h₀
  rw [sum_eq_single t]
  · rw [ite_eq_left ht.symm]
    congr 1
    have hcast : (t.val : ℝ) = ((h % (r : ℤ) : ℤ) : ℝ) := by exact_mod_cast ht
    rw [hcast, phase_emod_ratio]
  · intro u _ hut
    have hu : h % (r : ℤ) ≠ (u.val : ℤ) := by
      intro he
      apply hut
      exact Fin.ext (by omega)
    rw [ite_eq_right hu, zero_mul]
  · simp

/-- The table diagonalizing the padded chirp consists of the bounded Bluestein
multipliers, with the frequency evaluated in turns per padded coordinate. -/
theorem paddedKernel_spectrum (a r : ℕ) [NeZero r] (ξ : Fin r) :
    circulantSpectrum (paddedKernel a r) ξ =
      Chirp.bluesteinMultiplier a ((ξ.val : ℝ) / r) := by
  unfold circulantSpectrum paddedKernel
  rw [folded_spectrum]
  simp only [Chirp.bluesteinMultiplier, Finset.mul_sum]
  refine sum_congr rfl fun h _ => ?_
  rw [mul_assoc, ← phase_add, phase_chirp]

theorem paddedKernel_spectrum_norm {a r : ℕ} (ha : 0 < a) [NeZero r] (ξ : Fin r) :
    ‖circulantSpectrum (paddedKernel a r) ξ‖ ≤ 40 :=
  (paddedKernel_spectrum a r ξ) ▸ Chirp.bluesteinMultiplier_bound ha _

/-- Applying the multiplier table between the padded forward Fourier
transform and its adjoint implements the convolution for every input. -/
theorem paddedKernel_fourier_sandwich (a r : ℕ) [NeZero r] :
    (normalizedFourier r)ᴴ *
      Matrix.diagonal (fun ξ : Fin r => Chirp.bluesteinMultiplier a ((ξ.val : ℝ) / r)) *
      normalizedFourier r = Matrix.circulant (paddedKernel a r) := by
  have hs := circulant_spectral_diagonal (paddedKernel a r)
  simp_rw [funext (paddedKernel_spectrum a r)] at hs
  rw [← hs]
  have hU : (normalizedFourier r)ᴴ * normalizedFourier r = 1 :=
    (normalizedFourier_unitary (a := r)).1
  calc
    _ = ((normalizedFourier r)ᴴ * normalizedFourier r) * Matrix.circulant (paddedKernel a r) *
        ((normalizedFourier r)ᴴ * normalizedFourier r) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.one_mul, Matrix.mul_one]

/-- The complete short Fourier matrix as the compression of the padded
Fourier multiplier circuit with the two chirp phase diagonals. -/
theorem bluestein_fourier_sandwich {a r : ℕ} [NeZero r] (ha : 0 < a)
    (hr : 2*a-1 ≤ r) :
    let E := firstCoords (show a ≤ r by omega)
    bluesteinDiagonal a * (Eᴴ * ((normalizedFourier r)ᴴ *
      diagonal (fun ξ : Fin r => Chirp.bluesteinMultiplier a ((ξ.val : ℝ) / r)) *
      normalizedFourier r) * E) * bluesteinDiagonal a = normalizedFourier a := by
  dsimp only
  rw [paddedKernel_fourier_sandwich, firstCoords_compression]
  exact normalizedFourier_padded ha hr

end ShortFourier

end NearSquareRoot
end Computability
end OAI

import OAI.Computability.NearSquareRoot.SynchronizedDilation
import OAI.Computability.NearSquareRoot.SynchronizedPaddedSymbol
import OAI.Computability.NearSquareRoot.SynchronizedRestoreCircuit

/-! # A short Fourier transform on borrowed coordinates

The circuit below uses the explicit bounded chirp multipliers on the padded
length, a two-coordinate unitary per frequency, and exactly 64 reflection
rounds. Its matrix is the desired normalized transform on the occupied
coordinates, extended by identity on all the borrowed coordinates.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix SynchronizedRestoration
open scoped Matrix

noncomputable section

/-- The dilation uses the same angle for every length and frequency. -/
def calibratedMultiplier (a r : ℕ) (ξ : Fin r) : ℂ :=
  Real.sin (Real.pi / 258) • Chirp.bluesteinMultiplier a ((ξ.val : ℝ) / r)

theorem calibratedMultiplier_lt_half {a r : ℕ} (ha : 0 < a) (ξ : Fin r) :
    ‖calibratedMultiplier a r ξ‖ < 1 / 2 := by
  rw [calibratedMultiplier, Complex.real_smul, mul_comm]
  convert Chirp.scaledMultiplier_lt_half ha ((ξ.val : ℝ) / r) using 1
  norm_num

/-- The active fiber inside the first half of the doubled padded array. -/
def activeFiber {a r : ℕ} (har : a ≤ r) := firstHalfInclusion (firstCoords har)

/-- Dilated, compressed chirp transform before amplitude amplification. -/
def shortDilation {a r : ℕ} (har : a ≤ r) :=
  chirpDilation (normalizedFourier r) (calibratedMultiplier a r)
    (firstCoords har) (bluesteinDiagonal a) (bluesteinDiagonal a)

theorem shortDilation_isometry {a r : ℕ} [NeZero r] (ha : 0 < a) (har : a ≤ r) :
    (shortDilation har)ᴴ * shortDilation har = 1 := by
  apply chirpDilation_isometry
  · exact (normalizedFourier_unitary (a := r)).1
  · exact (normalizedFourier_unitary (a := r)).2
  · intro i
    exact (calibratedMultiplier_lt_half ha i).le.trans (by norm_num)
  · exact firstCoords_isometry _
  · exact bluesteinDiagonal_isometry _
  · exact bluesteinDiagonal_isometry _

theorem shortDilation_compression {a r : ℕ} [NeZero r] (ha : 0 < a) (hr : 2*a-1 ≤ r)
    (har : a ≤ r) :
    (activeFiber har)ᴴ * shortDilation har * activeFiber har =
      Real.sin (Real.pi / 258) • normalizedFourier a := by
  have hs : diagonal (calibratedMultiplier a r) =
      Real.sin (Real.pi / 258) • diagonal (fun ξ : Fin r =>
        Chirp.bluesteinMultiplier a ((ξ.val : ℝ) / r)) := by
    rw [← Matrix.diagonal_smul]
    rfl
  rw [activeFiber, shortDilation, compress_chirpDilation _ _ _ _ _ (firstCoords_isometry har), hs]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [bluestein_fourier_sandwich ha hr]

/-- The actual short-transform circuit. The input can contain arbitrary data on
the borrowed coordinates, even from a previous transform batch. -/
def restoredShortTransform {a r : ℕ} [NeZero a] (har : a ≤ r) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) ℂ :=
  let E := activeFiber har
  let B := amplifiedCircuit E (shortDilation har) 64
  extend E (diagonal fun t : Fin a => chirp a t.val) * Bᴴ *
    extend E (diagonal (chirpSpectrum a)) * B *
    extend E (diagonal fun t : Fin a => chirp a (-(t.val : ℤ)))

/-- The unconditional matrix identity for one short transform, valid for every
positive occupied size and padded size satisfying the no-collision condition. -/
theorem restoredShortTransform_eq {a r : ℕ} [NeZero a] [NeZero r] (hr : 2*a-1 ≤ r)
    (har : a ≤ r) :
    restoredShortTransform har = extend (activeFiber har) (normalizedFourier a) := by
  apply restore_short_fourier
  · exact firstHalfInclusion_isometry _ (firstCoords_isometry har)
  · exact shortDilation_isometry (NeZero.pos a) har
  · norm_num only [Nat.cast_ofNat, show (4 : ℝ)*64 + 2 = 258 by norm_num]
    exact shortDilation_compression (NeZero.pos a) hr har

end
end ShortFourier

end NearSquareRoot
end Computability
end OAI

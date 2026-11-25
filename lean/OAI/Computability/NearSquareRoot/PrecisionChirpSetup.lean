import OAI.Computability.NearSquareRoot.PrecisionChirpSumProgram
import OAI.Computability.NearSquareRoot.PrecisionChirpIndexWords

/-! # Fixed-tape polynomial setup of the two normalized chirp tables -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChirpTable

open IntegerMultiplication Code Strip Staff Carry Dusk Grid

attribute [local irreducible] Nat.clog sumWidth sumPrecision

set_option maxHeartbeats 2000000

variable {J : Type} {s : Regime J} {a target : J → ℕ}

/-- All padded-chirp multipliers at the supplied frequencies, with the cost of
direction generation and finite-record preparation included in `Has`. -/
theorem prepareBluestein {r ξ : J → ℕ} (A : Realizes s a) (P : Realizes s target)
    (R : Figure s r) (F : Figure s ξ) (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) :
    ∃ v : (i : J) → Grain (sumWidth (a i) (target i)), s.Has (fun i => mark (k := sumWidth (a i) (target i)) (v i)) ∧
      ∀ i, ‖meaning (sumPrecision (a i) (target i)) (sumWidth (a i) (target i)) (v i) -
        Chirp.bluesteinMultiplier (a i) ((ξ i : ℝ) / r i)‖ ≤ 1/(2:ℝ)^target i := by
  obtain ⟨B,built,approx⟩ := bluesteinRows A R F (sumPrecision_realizes A P) (sumWidth_realizes A P)
    ha hr (fun i => root_headroom ..)
  refine prepareNormalizedSum A P ha B built _ (fun i => Chirp.bluesteinMultiplier_bound (ha i) _) ?_
  intro i q output
  exact bluestein_guarded (ha i) (hr i) (ξ i) (target i) _ _ _ (fun j => by
    simpa [Star.drop_, displacement, one_div, inv_pow, div_eq_mul_inv] using approx i j)

/-- Entries of the restoration diagonal generated from the common axis
descriptor, with the parity correction at odd lengths. -/
theorem prepareSpectrum (A : Realizes s a) (P : Realizes s target)
    (ξ : (i : J) → Fin (a i)) (F : Figure s (fun i => (ξ i).val)) [∀ i, NeZero (a i)] :
    ∃ v : (i : J) → Grain (sumWidth (a i) (target i)), s.Has (fun i => mark (k := sumWidth (a i) (target i)) (v i)) ∧
      ∀ i, ‖meaning (sumPrecision (a i) (target i)) (sumWidth (a i) (target i)) (v i) -
        ShortFourier.chirpSpectrum (a i) (ξ i)‖ ≤ 1/(2:ℝ)^target i := by
  have ha i := NeZero.pos (a i)
  obtain ⟨B,built,approx⟩ := spectrumRows A F (sumPrecision_realizes A P) (sumWidth_realizes A P)
    ha (fun i => root_headroom ..)
  refine prepareNormalizedSum A P ha B built _ (fun i => by rw [ShortFourier.chirpSpectrum_norm]; norm_num) ?_
  intro i q output
  exact spectrum_guarded (ξ i) (target i) _ _ _ (fun j => by
    simpa [Star.drop_, one_div, inv_pow, div_eq_mul_inv] using approx i j)

/-- Prepare the complete Bluestein scalar table in frequency order. The number
of enlarged frequencies is provided in unary, as its enumeration is polynomial
in the shape parameters. -/
theorem prepareBluesteinTable {r : J → ℕ} (A : Realizes s a) (P : Realizes s target)
    (R : Realizes s r) (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) :
    ∃ v : (i : J) → Fin (r i) → Grain (sumWidth (a i) (target i)),
      s.Has (fun i => List.ofFn fun j => mark (k := sumWidth (a i) (target i)) (v i j)) ∧
      ∀ i j, ‖meaning (sumPrecision (a i) (target i)) (sumWidth (a i) (target i)) (v i j) -
        Chirp.bluesteinMultiplier (a i) ((j.val : ℝ) / r i)‖ ≤ 1/(2:ℝ)^target i := by
  obtain ⟨v, built, approx⟩ := prepareBluestein (landing r R _ A) (landing r R _ P)
    (Figure.of_spoken (landing r R _ R)) (Figure.of_spoken (floor_ r R))
    (fun i => ha i.1) (fun i => hr i.1)
  exact ⟨fun i j => v ⟨i,j⟩, harvest r R (fun i j => mark (v ⟨i,j⟩)) built,
    fun i j => approx ⟨i,j⟩⟩

/-- Prepare the complete restored spectral diagonal in increasing frequency order. -/
theorem prepareSpectrumTable (A : Realizes s a) (P : Realizes s target) [∀ i, NeZero (a i)] :
    ∃ v : (i : J) → Fin (a i) → Grain (sumWidth (a i) (target i)),
      s.Has (fun i => List.ofFn fun j => mark (k := sumWidth (a i) (target i)) (v i j)) ∧
      ∀ i j, ‖meaning (sumPrecision (a i) (target i)) (sumWidth (a i) (target i)) (v i j) -
        ShortFourier.chirpSpectrum (a i) j‖ ≤ 1/(2:ℝ)^target i := by
  let _ : ∀ i : Across a, NeZero ((a ∘ at_ a) i) := fun t => inferInstanceAs (NeZero (a t.1))
  obtain ⟨v, built, approx⟩ := prepareSpectrum (landing a A _ A) (landing a A _ P)
    (fun i => i.2) (Figure.of_spoken (floor_ a A))
  exact ⟨fun i j => v ⟨i,j⟩, harvest a A (fun i j => mark (v ⟨i,j⟩)) built,
    fun i j => approx ⟨i,j⟩⟩

end ChirpTable

end NearSquareRoot
end Computability
end OAI

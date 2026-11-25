import OAI.Computability.NearSquareRoot.PrecisionChirpRoots
import OAI.Computability.IntegerMultiplication.Winds

/-! # Computing complete rows of chirp-root words

Each row is constructed by the fixed-tape setup operations of P192, including
signed multiplication, Euclidean reduction and generation of complex roots
at the requested precision. The Bluestein loop traverses its displacements
from `1-a` to `a-1`; the spectrum loop traverses the occupied fiber.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChirpTable

open IntegerMultiplication
open Code Strip Staff Carry Brief
open Dusk Grid

variable {J : Type} {s : Regime J}

theorem bluesteinIndex_figure {a r ξ : J → ℕ} {h : J → ℤ}
    (A : Figure s a) (R : Figure s r) (F : Figure s ξ) (H : Signed s h)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) :
    Figure s (fun i => bluesteinIndex (a i) (r i) (ξ i) (h i)) := by
  let den := (((Figure.natural (r := s) 2).multiplied A).multiplied R)
  have left := ((H.multiplying H).negative.multiplying (Signed.up R))
  have right := (((Signed.fixed 2).multiplying (Signed.up A)).multiplying (Signed.up F)).multiplying H
  simpa only [bluesteinIndex, residue, pow_two] using
    (left.adding right).modulo den (fun i => by positivity [ha i, hr i])

theorem spectrumIndex_figure {a ξ h : J → ℕ}
    (A : Figure s a) (F : Figure s ξ) (H : Figure s h) (ha : ∀ i, 0 < a i) :
    Figure s (fun i => spectrumIndex (a i) (ξ i) (h i)) := by
  let den := (Figure.natural (r := s) 2).multiplied A
  have first := ((Signed.fixed 2).multiplying (Signed.up F)).multiplying (Signed.up H)
  have sq := (Signed.up H).multiplying (Signed.up H)
  have last := (Signed.up (A.modded (Figure.natural 2))).multiplying (Signed.up H)
  simpa only [spectrumIndex, residue, pow_two] using
    ((first.subtraction sq).subtraction last).modulo den (fun i => by positivity [ha i])

private theorem figure_landing {m u : J → ℕ} (M : Realizes s m) (U : Figure s u) :
    Figure (signal m M) (u ∘ at_ m) := by
  obtain ⟨x, hx, he⟩ := U
  exact ⟨x ∘ at_ m, sendRoof m M _ hx, fun i => he i.1⟩

/-- All fixed-precision complex phase words needed for one zero-extended
Bluestein multiplier. `Has` supplies a single P192 polynomial-time setup
program for the whole list in its loop order. -/
theorem bluesteinRows {a r ξ frac w : J → ℕ}
    (A : Realizes s a) (R : Figure s r) (F : Figure s ξ)
    (P : Realizes s frac) (W : Realizes s w)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i)
    (guard : ∀ i, (2:ℝ)*2^(frac i)+2 < 2^(w i)) :
    ∃ B : (i : J) → Fin (2*a i-1) → Grain (w i),
      s.Has (fun i => List.ofFn (fun j => mark (B i j))) ∧
      ∀ i j, ‖meaning (frac i) (w i) (B i j) -
        Fourier.phase (2*a i*r i) (bluesteinIndex (a i) (r i) (ξ i) ((j.val : ℤ)+1-a i) : ℤ)‖
          ≤ 3 * Star.drop_ (frac i) := by
  let m i := 2*a i-1
  have M : Realizes s m := ((Realizes.fix 2).times A).minused (.fix 1)
  let E := signal m M
  have A' := figure_landing M (Figure.of_spoken A)
  have R' := figure_landing M R
  have F' := figure_landing M F
  have signedH : Signed E (fun t : Across m => (t.2.val : ℤ) + 1 - a t.1) :=
    (((Signed.up (Figure.of_spoken (floor_ m M))).adding (.fixed 1)).subtraction (Signed.up A'))
  have hidx := bluesteinIndex_figure A' R' F' signedH (fun t => ha t.1) (fun t => hr t.1)
  have hden := ((Figure.natural (r := E) 2).multiplied A').multiplied R'
  obtain ⟨v, built, approx⟩ := Star.direction (frac ∘ at_ m) (w ∘ at_ m)
    (landing m M _ P) (landing m M _ W) (fun t => guard t.1) hidx hden
    (fun t => by positivity [ha t.1, hr t.1])
    (fun t => (bluesteinIndex_lt (ha t.1) (hr t.1) _ _).le)
  exact ⟨fun i j => v ⟨i,j⟩, harvest m M (fun i j => mark (v ⟨i,j⟩)) built,
    fun i j => approx ⟨i,j⟩⟩

/-- All phase words needed by the spectral diagonal at one frequency. -/
theorem spectrumRows {a ξ frac w : J → ℕ}
    (A : Realizes s a) (F : Figure s ξ) (P : Realizes s frac) (W : Realizes s w)
    (ha : ∀ i, 0 < a i) (guard : ∀ i, (2:ℝ)*2^(frac i)+2 < 2^(w i)) :
    ∃ B : (i : J) → Fin (a i) → Grain (w i),
      s.Has (fun i => List.ofFn (fun j => mark (B i j))) ∧
      ∀ i j, ‖meaning (frac i) (w i) (B i j) -
        Fourier.phase (2*a i) (spectrumIndex (a i) (ξ i) j.val : ℤ)‖
          ≤ 3 * Star.drop_ (frac i) := by
  have A' := figure_landing A (Figure.of_spoken A)
  have F' := figure_landing A F
  have H := Figure.of_spoken (floor_ a A)
  have hidx := spectrumIndex_figure A' F' H (fun t => ha t.1)
  have hden := (Figure.natural (r := signal a A) 2).multiplied A'
  obtain ⟨v, built, approx⟩ := Star.direction (frac ∘ at_ a) (w ∘ at_ a)
    (landing a A _ P) (landing a A _ W) (fun t => guard t.1) hidx hden
    (fun t => by positivity [ha t.1])
    (fun t => (spectrumIndex_lt (ha t.1) _ _).le)
  exact ⟨fun i j => v ⟨i,j⟩, harvest a A (fun i j => mark (v ⟨i,j⟩)) built,
    fun i j => approx ⟨i,j⟩⟩

end ChirpTable

end NearSquareRoot
end Computability
end OAI

import OAI.LinearAlgebra.FiniteFourier.WorkingLengthWord
import OAI.LinearAlgebra.FiniteFourier.WorkingShortWord
import OAI.LinearAlgebra.FiniteFourier.WorkingGroup.WorkingAxisWord

/-! # Two-scale Fourier words for a group of small axes

The short radix-power transforms give occupied words for the small coprime
factors of each working length. Good's permutation and the occupied-fibers
lemma give a transform at that length. Applying the one-factor lemma again
realizes the prescribed grid factor. Finally the occupied-fibers lemma
synchronizes these words across all axes of the group.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix
open scoped BigOperators

/-- Absolute multiplier in the depth bound obtained by two applications of
the occupied-fibers lemma and the single-factor construction. -/
def workingGridDepthConstant : ℕ :=
  fiberDepthFactor 170 * (336 * fiberDepthFactor 14 * 24000 + 1463)

namespace WorkingGroup

variable {K : Type*} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {a : ι → ℕ} {t : ℕ} (w : WorkingGroup K a t)

/-- Every group with the prescribed working lengths has an extension-field word
on `170*B` registers of depth bounded by an absolute multiple of `1+log₂(1+t)`.
The data transform is exactly the base matrix embedded in the cyclotomic field. -/
theorem grid_word (ha : ∀ i, 2 ≤ a i) {A : ∀ i, Matrix (Fin (a i)) (Fin (a i)) K}
    (hA : ∀ i, GridFactor (A i)) :
    OccupiedWord (Fin (169 * ∏ i, a i))
      (workingGridDepthConstant * (1 + Nat.clog 2 (1+t)))
      ((gridTensor A).map (algebraMap K (CyclotomicField w.order K))) := by
  let E := CyclotomicField w.order K
  obtain ⟨ζ, -, hroot, -⟩ := w.exists_roots
  let u i := ζ ^ (w.order / w.length i)
  have hF i : OccupiedWord (Fin (13 * w.length i)) (fiberDepthFactor 14 * shortWordDepth t)
      (geometricMatrix (w.length i) (u i)) :=
    w.length_fourier_word i (hroot i) (fun m hm z hz => w.short_fourier_word i hm hz)
  have haxis (i : ι) : OccupiedWord (Fin (169*a i)) (336*(fiberDepthFactor 14 * shortWordDepth t)+1463)
      ((A i).map (algebraMap K E)) := by
    exact w.axis_word_of_length_word i (hroot i) (hF i) ((hA i).map (algebraMap K E))
  have hsync := occupiedWord_gridTensor (c := 170) (by decide)
    (P := fun i => Fin (a i)) (by simpa using ha) (W := fun i => Fin (169 * a i))
    (fun i => by simp [Nat.mul_comm]) haxis
  rw [map_gridTensor]
  have haux : Fintype.card (∀ i, Fin (a i)) * (170-1) = 169 * ∏ i, a i := by
    simp [Fintype.card_pi, Nat.mul_comm]
  rw [haux] at hsync
  apply LayerWord.pad (hA := hsync)
  dsimp only [workingGridDepthConstant, shortWordDepth]
  rw [Nat.mul_assoc (fiberDepthFactor 170)]
  apply Nat.mul_le_mul_left
  rw [Nat.add_mul, Nat.mul_assoc (336 * fiberDepthFactor 14), Nat.mul_assoc 336]
  exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (by omega)) _

end WorkingGroup

end FiniteFourier
end LinearAlgebra
end OAI

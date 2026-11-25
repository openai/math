import OAI.Computability.NearSquareRoot.SynchronizedShortAxis
import OAI.Computability.NearSquareRoot.SynchronizedAxisProduct
import OAI.Computability.NearSquareRoot.SynchronizedBlocks

/-! # The exact logarithmic-depth word on a block of four to seven short axes

This combines the short restored Fourier circuit, fifteen nonoverlapping
batches per axis, and successive passes on all the axes of the block.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix Finset SynchronizedBorrowing SynchronizedBlocks SynchronizedPadding ResidueFourier

/-- The restored circuit relocated to the chosen active-and-spare coordinates. -/
theorem fiberFourier_word {a b c : ℕ} [NeZero a] (hb : 8 ≤ b) (he : Even (b*(a+c))) :
    HasShortWord (fiberMatrix (c := c) b (normalizedFourier a)) (45000*(Nat.clog 2 a + 2)) := by
  let k := paddedLog a
  have har : a ≤ 2^k := by
    have := paddedLog_covers a
    have := NeZero.pos a
    dsimp [k]
    omega
  obtain ⟨hr,hU⟩ := shortAxis_depth a
  have hl := hU.relocate (auxiliaryLayout har)
  rw [auxiliaryLayout_extend har] at hl
  simpa [← Nat.mul_assoc] using fiberMatrix_word (c := c) hb hr.le he (normalizedFourier a) hl

private theorem spectator_card {m : ℕ} (a c w : Fin m → ℕ) [∀ i, NeZero (a i)]
    (shape : ∀ i, a i + c i = 2 ^ w i) (i : Fin m) :
    Fintype.card (Spectators a c i) = ∏ t ∈ univ.erase i, 2 ^ w t := by
  classical
  rw [prod_subtype (univ.erase i) (p := fun t ↦ t ≠ i) (F := inferInstance) (by simp) (fun t ↦ 2 ^ w t)]
  simp [Spectators, BlockAxis, Fintype.card_pi, shape]

/-- The complete local word, on the original occupied and unoccupied residue
addresses within the block. Each stage retains its primitive gate kind. -/
theorem blockFourier_word {d L : ℕ} (a c w : Fin d → ℕ) [∀ i, NeZero (a i)]
    (_hd : 4 ≤ d) (hwidth : ∀ i, 0 < w i) (hmax : ∀ i, w i ≤ L)
    (hshape : ∀ i, a i + c i = 2 ^ w i) (j : Fin (d / 4)) :
    HasShortWord (tensorMatrix (fun i : Fin (count j) ↦
      axisPadding (b := Fin (c (axis j i))) (axisMatrix (a (axis j i))))) (315000*(L+2)) := by
  let a' := a ∘ axis j
  let c' := c ∘ axis j
  let w' := w ∘ axis j
  let _ (i : Fin (count j)) : NeZero (a' i) := inferInstanceAs (NeZero (a (axis j i)))
  have shape (i : Fin (count j)) : a' i + c' i = 2 ^ w' i := hshape _
  have localWord (i : Fin (count j)) :
      HasShortWord (fiberMatrix (c := c' i) (Fintype.card (Spectators a' c' i))
        (normalizedFourier (a' i))) (45000*(L+2)) := by
    have cap : a' i ≤ 2 ^ w' i := by rw [← shape]; omega
    have hlog : Nat.clog 2 (a' i) ≤ w' i := Nat.clog_le_of_le_pow cap
    have even : Even (a' i + c' i) := by
      rw [shape]
      exact Even.pow_of_ne_zero (by decide : Even 2) (Nat.ne_of_gt (hwidth _))
    apply (fiberFourier_word ?_ (even.mul_left _)).mono
    · have := hmax (axis j i)
      change w' i ≤ L at this
      omega
    · rw [spectator_card a' c' w' shape]
      exact spectatorFibers_ge_eight w hwidth j i
  apply (blockTensor_word a' c' localWord).mono
  calc
    count j * (45000*(L+2)) ≤ 7 * (45000*(L+2)) := Nat.mul_le_mul_right _ (count_bounds j).2
    _ = _ := by ring

end ShortFourier

end NearSquareRoot
end Computability
end OAI

import OAI.Optimization.LinearProgramming.RAM.Code
import OAI.Optimization.LinearProgramming.PrimalDual.Layout

/-! The saved objective and primal point in the first and second oracle return layouts. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open RAM

/-- Dropping the copied primal feasibility input exposes the contiguous pair of
vectors, including empty vectors. -/
theorem savedPair_suffix {K : Type*} {m d : ℕ} (A : Matrix (Fin m) (Fin d) K)
    (b : Fin m → K) (c x₀ : Fin d → K) :
    ((lpInput A b ++ List.ofFn c) ++ List.ofFn x₀).drop (m*d+m) =
      List.ofFn c ++ List.ofFn x₀ := by
  rw [List.append_assoc,← lpInput_length A b, List.drop_left]

private theorem pair_read_left {K : Type*} [Zero K] {d : ℕ} (c x₀ : Fin d → K) (i : Fin d) :
    ((List.ofFn c ++ List.ofFn x₀)[i.val]?).getD 0 = c i := by
  rw [List.getElem?_append_left (by simp)]
  simp [i.isLt]

private theorem pair_read_right {K : Type*} [Zero K] {d : ℕ} (c x₀ : Fin d → K) (i : Fin d) :
    ((List.ofFn c ++ List.ofFn x₀)[d+i.val]?).getD 0 = x₀ i := by
  rw [List.getElem?_append_right (by simp)]
  simp [i.isLt]

/-- Immediately after the original input has been copied and the returned feasible
point appended, the subwindow at the objective's offset is exactly the saved pair. -/
theorem savedPair_firstWindow {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (c x₀ : Fin d → ℚ) (s : Memory ℚ) (orig : ℕ)
    (original : ∀ j < m*d+m+d, s.data (orig+j) = optInputWord A b c j)
    (point : ∀ i : Fin d, s.data (orig+(m*d+m+d)+i.val) = x₀ i) :
    ∀ j < 2*d, s.data ((orig+m*d+m)+j) = ((List.ofFn c ++ List.ofFn x₀)[j]?).getD 0 := by
  intro j h
  by_cases hj : j < d
  · let i : Fin d := ⟨j,hj⟩
    have hcopy := original (m*d+m+j) (by omega)
    rw [show orig+m*d+m+j = orig+(m*d+m+j) by omega, hcopy]
    exact (optInputWord_obj A b c i).trans (pair_read_left c x₀ i).symm
  · let i : Fin d := ⟨j-d,by omega⟩
    have he : j = d+i.val := by dsimp [i]; omega
    rw [he]
    rw [show orig+m*d+m+(d+i.val) = orig+(m*d+m+d)+i.val by omega]
    exact (point i).trans (pair_read_right c x₀ i).symm

/-- Reading the two halves of the interleaved high-memory frame after the second
return recovers the objective and the feasible base point at their exact addresses. -/
theorem savedPair_secondWindow {d : ℕ} (c x₀ : Fin d → ℚ) (s : Memory ℚ)
    (window : ∀ j < 2*d, s.data (3+2*j) = ((List.ofFn c ++ List.ofFn x₀)[j]?).getD 0) :
    (∀ i : Fin d, s.data (3+2*i.val) = c i) ∧
      (∀ i : Fin d, s.data (3+2*(d+i.val)) = x₀ i) := by
  constructor
  · intro i; exact (window i.val (by have := i.isLt; omega)).trans (pair_read_left c x₀ i)
  · intro i; exact (window (d+i.val) (by have := i.isLt; omega)).trans (pair_read_right c x₀ i)

end PrimalDual
end LinearProgramming
end Optimization
end OAI

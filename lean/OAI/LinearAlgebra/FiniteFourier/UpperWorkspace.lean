import OAI.LinearAlgebra.FiniteFourier.Upper
import OAI.LinearAlgebra.FiniteFourier.OccupiedWord

/-! # Reading the data registers after a packed occupied-word computation -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- Discard the workspace coordinates in every batch. -/
theorem complexity_data_of_batches {K I W D : Type*} [Field K] [Fintype I] [Fintype W]
    [DecidableEq W] [Fintype D] [DecidableEq D] (T : Matrix I I K) :
    complexity (Matrix.blockDiagonal (fun _ : D => T)) ≤
      complexity (Matrix.blockDiagonal (fun _ : D => Matrix.fromBlocks T 0 0 (1 : Matrix W W K))) := by
  classical
  let f : I × D ↪ (I ⊕ W) × D := Function.Embedding.inl.prodMap (Function.Embedding.refl _)
  apply (complexity_le_iff ..).2
  convert (realizableAtMost_complexity _).submatrix f f using 1
  ext ⟨i,d⟩ ⟨j,u⟩
  change (if d = u then T i j else 0) = (if d = u then T i j else 0)
  rfl

theorem real_clog_two_le (N : ℕ) (hN : 1 ≤ N) :
    (Nat.clog 2 N : ℝ) ≤ Real.logb 2 N + 1 := by
  rw [← Real.natCeil_logb_natCast]
  exact (Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) (by exact_mod_cast hN))).le

/-- The rounded logarithmic depth remains within a factor two after conversion
from natural to real exponents. -/
theorem clog_depth_le (t : ℕ) :
    (1 + Nat.clog 2 (1+t) : ℕ) ≤ 2 * (1 + Real.logb 2 (1 + (t : ℝ))) := by
  have h := real_clog_two_le (1+t) (by omega)
  push_cast at h ⊢
  have ht : 0 ≤ Real.logb 2 (1 + (t : ℝ)) := Real.logb_nonneg (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) t])
  linarith

end FiniteFourier
end LinearAlgebra
end OAI

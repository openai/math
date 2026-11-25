import OAI.Computability.NearSquareRoot.KernelPassRectSum

/-! # One charged rectangle in a restricted binary template

Collect source labels into the internal rows, run the common plan once per
internal row, then broadcast each result to its selected target labels.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Rect

open Matrix Finset
open scoped BigOperators

variable {A : ℕ} {L W : Type} [Fintype L] [Fintype W] [DecidableEq L] [DecidableEq W]

private def collect (S : Finset L) (B : W → W → Coefficient) (srcIn : L → Plan A 1 1)
    (k : W) (v : L × W) : Plan A 1 1 :=
  if v.1 ∈ S then times (B k v.2) (srcIn v.1) else emptyPlan

private def fanout (T : Finset L) (weight : Coefficient) (dstOut : L → Plan A 1 1)
    (w : L × W) (k : W) : Plan A 1 1 :=
  if w.1 ∈ T ∧ w.2 = k then times weight (dstOut w.1) else emptyPlan

variable (S T : Finset L) (weight : Coefficient) (B : W → W → Coefficient)
  (srcIn dstOut : L → Plan A 1 1) (common : Plan A 1 1)

/-- The common transform acts on a bank indexed only by the internal rows. -/
noncomputable def charged : On A (L × W) (L × W) :=
  (entries (fanout T weight dstOut)).seq
    ((diagonal (fun _ : W => common)).seq (entries (collect S B srcIn)))

theorem calls_charged (hsrc : ∀ v, (srcIn v).calls = 0)
    (hdst : ∀ w, (dstOut w).calls = 0) :
    (charged S T weight B srcIn dstOut common).calls = Fintype.card W * common.calls := by
  simp [charged, Plan.calls, calls_entries, calls_diagonal, collect, fanout, apply_ite, hsrc, hdst]

private theorem oneRow_zero (h : ℕ) : oneRow (0 : RowMatrix A h 1 1) = 0 := rfl

theorem block_charged (h : ℕ) (w v : L) (k l : W) :
    block (I := L × W) (O := L × W) (charged S T weight B srcIn dstOut common) h (w,k) (v,l) =
    if v ∈ S ∧ w ∈ T then value weight • value (B k l) •
      (oneRow ((dstOut w).eval h) * oneRow (common.eval h) * oneRow ((srcIn v).eval h)) else 0 := by
  unfold charged
  rw [block_seq (J := W), block_seq (J := W), block_entries, block_diagonal, block_entries,
    Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, Matrix.of_apply]
  by_cases hv : v ∈ S <;> by_cases hw : w ∈ T <;>
    simp [collect, fanout, hv, hw, apply_ite, oneRow_zero, matrix_times, ite_mul, Matrix.mul_assoc]
  exact smul_comm _ _ _

end KernelPass.Rect

end NearSquareRoot
end Computability
end OAI

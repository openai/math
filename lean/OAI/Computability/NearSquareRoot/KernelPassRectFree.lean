import OAI.Computability.NearSquareRoot.KernelPassRectSum

/-! # Sharing the endpoint transforms of a free rectangle

Both endpoint banks are applied once, around a weighted sum over queries
and clock rows. All queries use the same source and destination plans.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Rect
open Matrix Finset
open scoped BigOperators

variable {A : ℕ} {L W J : Type} [Fintype L] [Fintype W] [Fintype J]
variable [DecidableEq L]

abbrev Single (A : ℕ) := Plan A 1 1

/-- Restrict the endpoint bank to the labels incident on the given side. -/
noncomputable def side (active : Finset L) (p : L → Single A) : On A (L × W) (L × W) :=
  diagonal (fun u : L × W => if u.1 ∈ active then p u.1 else emptyPlan)

theorem calls_side (active : Finset L) (p : L → Single A) :
    (side (W := W) active p).calls = Fintype.card W * ∑ v ∈ active, (p v).calls := by
  classical
  simp [side, calls_diagonal, Fintype.sum_prod_type, apply_ite Plan.calls, ← mul_sum]

noncomputable def free (src dst : Finset L) (weight : Coefficient)
    (B : J → W → W → Coefficient) (S T : L → Single A) (M : J → L → L → Single A) :
    On A (L × W) (L × W) :=
  (side dst T).seq ((entries (fun (b a : L × W) =>
    times weight (total fun j => times (B j b.2 a.2) (M j b.1 a.1)))).seq (side src S))

theorem calls_free (src dst : Finset L) (weight : Coefficient)
    (B : J → W → W → Coefficient) (S T : L → Single A) (M : J → L → L → Single A)
    (hm : ∀ j w v, (M j w v).calls = 0) :
    (free src dst weight B S T M).calls =
      Fintype.card W * ((∑ w ∈ dst, (T w).calls) + ∑ v ∈ src, (S v).calls) := by
  simp [free, Plan.calls, calls_entries, calls_total, hm, calls_side, Nat.mul_add]

theorem oneRow_total {K : Type} [Fintype K] (p : K → Single A) (h : ℕ) :
    oneRow ((total p).eval h) = ∑ k, oneRow ((p k).eval h) := by
  ext y x
  simp only [oneRow, eval_total, Matrix.sum_apply]

@[simp] theorem oneRow_zero {h : ℕ} : oneRow (0 : RowMatrix A h 1 1) = 0 := rfl

theorem block_free (src dst : Finset L) (weight : Coefficient)
    (B : J → W → W → Coefficient) (S T : L → Single A) (M : J → L → L → Single A)
    (h : ℕ) (w v : L) (k l : W) :
    block (I := L × W) (O := L × W) (free src dst weight B S T M) h (w,k) (v,l) =
      if v ∈ src ∧ w ∈ dst then value weight •
        ∑ j, value (B j k l) • (oneRow ((T w).eval h) * oneRow ((M j w v).eval h) *
          oneRow ((S v).eval h))
      else 0 := by
  classical
  unfold free side
  rw [block_seq (J := L × W), block_seq (J := L × W), block_diagonal,
    block_entries, block_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  by_cases hv : v ∈ src <;> by_cases hw : w ∈ dst
  · simp [hv, hw, matrix_times, oneRow_total, Matrix.mul_sum, Matrix.sum_mul, mul_assoc]
  all_goals simp [hv, hw]

end KernelPass.Rect

end NearSquareRoot
end Computability
end OAI

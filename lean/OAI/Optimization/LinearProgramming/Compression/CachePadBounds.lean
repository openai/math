import OAI.Optimization.LinearProgramming.Compression.NativeCache

/-! Padding an epoch query for the shared magnitude oracle preserves its actual exponent
budget and its coefficient widths. The trailing affine constant stays in the last slot. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

@[simp] theorem padEpochQuery_sum_abs {g : ℕ} (a : Fin (g+1) → ℤ) :
    (∑ i, |padEpochQuery a i|) = ∑ i, |a i| := by
  simp only [padEpochQuery,Fin.sum_univ_castSucc,Fin.snoc_last,Fin.snoc_castSucc,abs_zero,add_zero]

@[simp] theorem padEpochQuery_sum_natAbs {g : ℕ} (a : Fin (g+1) → ℤ) :
    (∑ i, (padEpochQuery a i).natAbs) = ∑ i, (a i).natAbs := by
  simp only [padEpochQuery,Fin.sum_univ_castSucc,Fin.snoc_last,Fin.snoc_castSucc,Int.natAbs_zero,add_zero]

theorem padEpochQuery_size {g b : ℕ} (a : Fin (g+1) → ℤ) (ha : ∀ i, (a i).natAbs.size ≤ b)
    (j : Fin ((g+1)+1)) : (padEpochQuery a j).natAbs.size ≤ b := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa [padEpochQuery] using ha (Fin.last g)
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [padEpochQuery]
    · simpa [padEpochQuery] using ha j.castSucc

end Compression
end LinearProgramming
end Optimization
end OAI

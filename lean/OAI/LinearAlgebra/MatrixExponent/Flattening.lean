import OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Law

namespace OAI.LinearAlgebra.MatrixExponent

/-- The square output flattening has rank equal to the area. -/
theorem rank_lower {F : Type*} [Field F] {n r : ℕ} (h : RankLE F n r) :
    n ^ 2 ≤ r := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [pow_two]
    exact Rectangle.RankLE.area h (Nat.pos_of_ne_zero hn)

end OAI.LinearAlgebra.MatrixExponent

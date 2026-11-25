import OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Law

/-! Square specializations of the rectangular rank constructions. -/

namespace OAI.LinearAlgebra.MatrixExponent

variable {F K : Type*} [Field F] [Field K] {n m r s : ℕ}

theorem rank_map (f : F →+* K) (h : RankLE F n r) : RankLE K n r :=
  Rectangle.RankLE.map h f

theorem rank_mul (h : RankLE F n r) (h' : RankLE F m s) : RankLE F (n * m) (r * s) :=
  Rectangle.RankLE.tensor h h'

theorem rank_pow (h : RankLE F n r) (k : ℕ) : RankLE F (n ^ k) (r ^ k) :=
  Rectangle.RankLE.pow h k

end OAI.LinearAlgebra.MatrixExponent

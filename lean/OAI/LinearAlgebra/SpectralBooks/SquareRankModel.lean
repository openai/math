import OAI.LinearAlgebra.MatrixExponent.FieldExtension
import OAI.LinearAlgebra.SpectralBooks.SquareExponent

/-! # Square tensor rank in the rational and division-free circuit models -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication.Foundation

/-- The output coordinates in a circuit are (row, column). In the cyclic tensor they are
(column, row). Swapping the last two indices identifies the two rank decompositions. -/
private theorem square_rank_iff {F : Type*} [Field F] {n r : ℕ} :
    MatrixExponent.RankLE F n r ↔ Tensor.RankAtMost (matrixTensor F n n n) r := by
  constructor
  · rintro ⟨a, b, c, h⟩
    refine ⟨a, b, fun i z => c i z.swap, ?_⟩
    funext x y z
    simpa [matrixTensor, Tensor.matrixCoefficients, Tensor.rankOne, and_comm, and_left_comm,
      eq_comm] using (h x y z.swap).symm
  · rintro ⟨a, b, c, h⟩
    refine ⟨a, b, fun i z => c i z.swap, ?_⟩
    intro x y z
    simpa [matrixTensor, Tensor.matrixCoefficients, Tensor.rankOne, and_comm, and_left_comm,
      eq_comm] using (congrFun (congrFun (congrFun h x) y) z.swap).symm

private theorem rpow_omega_le_asymptoticRank (F : Type*) [Field F] {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ MatrixExponent.omega F ≤ asymptoticRank (matrixTensor F n n n) := by
  apply le_ciInf
  intro k
  rw [tensorRank_matrixTensor_power]
  apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
    (show 0 < (k : ℝ) + 1 by positivity)).mpr
  rw [← Nat.cast_succ, Real.rpow_natCast, Real.rpow_pow_comm (Nat.cast_nonneg n), ← Nat.cast_pow]
  by_contra! h
  let m := n ^ (k + 1)
  have hr := square_rank_iff.mpr (rankAtMost_tensorRank (matrixTensor F m m m))
  exact (lt_irrefl (MatrixExponent.omega F)) (MatrixExponent.omega_lt_of_rank
    (hn.trans (le_self_pow (by omega) (by omega))) hr h)

/-- Finite square tensor ranks determine the same exponent for both circuit models. -/
theorem formalOmega_square_eq_omega (F : Type*) [Field F] :
    formalOmega F 1 1 1 = MatrixExponent.omega F := by
  apply le_antisymm
  · by_contra! h
    obtain ⟨n, r, hn, rank, small⟩ := MatrixExponent.omega_lt_iff_rank.mp h
    have le := tensorRank_le_of_rankAtMost (square_rank_iff.mp rank)
    exact (not_lt_of_ge ((rpow_formalOmega_le_tensorRank F hn).trans (Nat.cast_le.mpr le))) small
  · have h := rpow_omega_le_asymptoticRank F (n := 2) (by decide)
    rw [square_asymptoticRank_eq_rpow_formalOmega F (by decide)] at h
    exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < (2 : ℕ))).mp h

end SpectralBooks
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.SpectralBooks.RankLimit

/-! # Powers of asymptotic tensor rank

Flattening a rectangular array of indices identifies iterated powers with a
single Kronecker power. The rank-root limit along the multiples of a positive
integer then gives the corresponding power of asymptotic rank.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open Filter MatrixMultiplication.Foundation
open scoped Topology

section

variable {F X Y Z : Type*} [Field F] [Fintype X] [Fintype Y]

private def flattenWord {A : Type*} (k n : ℕ) :
    (Fin k → Fin n → A) ≃ (Fin (k * n) → A) where
  toFun x i := x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  invFun x i j := x (finProdFinEquiv (i, j))
  left_inv x := by funext i j; simp
  right_inv x := by funext i; exact congrArg x (finProdFinEquiv.apply_symm_apply i)

/-- Iterated tensor powers have the rank of the power at the product of their indices. -/
theorem tensorRank_power_power (T : Tensor F X Y Z) (n k : ℕ) :
    tensorRank (Tensor.power (Tensor.power T n) k) = tensorRank (Tensor.power T (k * n)) := by
  have heq : Tensor.power (Tensor.power T n) k = Tensor.pullback
      (flattenWord k n) (flattenWord k n) (flattenWord k n) (Tensor.power T (k * n)) := by
    funext x y z
    simp only [Tensor.power, Tensor.pullback]
    rw [← Fintype.prod_prod_type']
    exact finProdFinEquiv.symm.prod_comp
      (fun i : Fin k × Fin n => T (x i.1 i.2) (y i.1 i.2) (z i.1 i.2)) |>.symm
  apply le_antisymm
  · rw [heq]
    exact tensorRank_le_of_rankAtMost ((rankAtMost_tensorRank _).pullback _ _ _)
  · apply tensorRank_le_of_rankAtMost
    have h := (rankAtMost_tensorRank (Tensor.power (Tensor.power T n) k)).pullback
      (flattenWord k n).symm (flattenWord k n).symm (flattenWord k n).symm
    convert h using 1
    funext x y z
    simp [heq, Tensor.pullback]

private theorem tensorRank_power_zero (T : Tensor F X Y Z) :
    tensorRank (Tensor.power T 0) = 1 := by
  apply le_antisymm
  · apply tensorRank_le_of_rankAtMost
    convert Tensor.rankOne_rankAtMost (fun _ => (1 : F)) (fun _ => (1 : F)) (fun _ => (1 : F))
      using 1
    funext x y z
    simp [Tensor.rankOne, Tensor.power]
  · by_contra! h
    have hz := rankAtMost_tensorRank (Tensor.power T 0)
    rw [show tensorRank (Tensor.power T 0) = 0 by omega] at hz
    obtain ⟨_, _, _, hzero⟩ := hz
    have he := congrFun (congrFun (congrFun hzero Fin.elim0) Fin.elim0) Fin.elim0
    simp [Tensor.power] at he

/-- Asymptotic rank is multiplicative on powers, including the zeroth power. -/
theorem asymptoticRank_power (T : Tensor F X Y Z) (n : ℕ) :
    asymptoticRank (Tensor.power T n) = asymptoticRank T ^ n := by
  apply tendsto_nhds_unique (tendsto_tensorRank_power_root _)
  by_cases hn : n = 0
  · subst n
    simp [tensorRank_power_power, tensorRank_power_zero]
  · have hseq : Tendsto (fun k : ℕ => k * n) atTop atTop := by
      apply tendsto_atTop_mono (f := id) _ tendsto_id
      intro k
      exact Nat.le_mul_of_pos_right k (Nat.pos_of_ne_zero hn)
    apply (((tendsto_tensorRank_power_root T).comp hseq).pow n).congr
    intro k
    simp only [Function.comp_apply, tensorRank_power_power, Nat.cast_mul]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    congr 1
    rw [mul_inv_rev]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp

end

end

end SpectralBooks
end LinearAlgebra
end OAI

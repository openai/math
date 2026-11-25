import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Ranks of matrices with two independent blocks -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- The rank of a rectangular block diagonal matrix is the sum of its block ranks. -/
theorem rank_fromBlocks_diagonal {F I J I' J' : Type*} [Field F] [Fintype J] [Fintype J']
    (A : Matrix I J F) (B : Matrix I' J' F) :
    (Matrix.fromBlocks A 0 0 B).rank = A.rank + B.rank := by
  let e := LinearEquiv.sumArrowLequivProdArrow I I' F F
  let d := LinearEquiv.sumArrowLequivProdArrow J J' F F
  have h : (Matrix.fromBlocks A 0 0 B).mulVecLin =
      e.symm.toLinearMap ∘ₗ (A.mulVecLin.prodMap B.mulVecLin) ∘ₗ d.toLinearMap := by
    apply LinearMap.ext
    intro x
    ext (i | i) <;> simp [Matrix.fromBlocks_mulVec, e, d] <;> rfl
  rw [Matrix.rank, h, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top, LinearEquiv.finrank_map_eq, LinearMap.range_prodMap,
    (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]
  rfl

end SpectralBooks
end LinearAlgebra
end OAI

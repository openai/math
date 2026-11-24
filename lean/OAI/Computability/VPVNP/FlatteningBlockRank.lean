import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Rank of a block diagonal flattening

The linear map of a block diagonal matrix acts independently on the two
coordinate blocks, so its range is isomorphic to the product of their ranges.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

/-- Ranks add under direct sums of rectangular matrices over any field. -/
theorem rank_fromBlocks_zero {k m n i j : Type*} [Field k]
    [Fintype n] [Fintype j] (A : Matrix m n k) (B : Matrix i j k) :
    (Matrix.fromBlocks A 0 0 B).rank = A.rank + B.rank := by
  let f := (Matrix.fromBlocks A 0 0 B).mulVecLin
  let g := A.mulVecLin.prodMap B.mulVecLin
  let e := LinearEquiv.sumArrowLequivProdArrow m i k k
  let d := LinearEquiv.sumArrowLequivProdArrow n j k k
  have h : e.toLinearMap.comp f = g.comp d.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · funext y
      change ((Matrix.fromBlocks A 0 0 B).mulVec x) (.inl y) = _
      simp [Matrix.fromBlocks_mulVec, g, d]
      rfl
    · funext y
      change ((Matrix.fromBlocks A 0 0 B).mulVec x) (.inr y) = _
      simp [Matrix.fromBlocks_mulVec, g, d]
      rfl
  have he : f.range.map e.toLinearMap = g.range := by
    rw [← LinearMap.range_comp, h, d.range_comp]
  calc
    _ = Module.finrank k g.range := (e.ofSubmodules f.range g.range he).finrank_eq
    _ = Module.finrank k (A.mulVecLin.range × B.mulVecLin.range) := by
      rw [show g.range = A.mulVecLin.range.prod B.mulVecLin.range from LinearMap.range_prodMap _ _]
      exact (Submodule.prodEquiv _ _).finrank_eq
    _ = _ := Module.finrank_prod

end WireTensor

end VPVNP
end Computability
end OAI

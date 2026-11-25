import OAI.LinearAlgebra.SpectralBooks.StretchPriceUpper
import OAI.LinearAlgebra.SpectralBooks.StretchProducts

/-! # Price of the diagonal used to control the tagged permutations -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Foundation
open scoped Classical

section
open PermutationControl PermutationStretch

/-- Equation `doubling-control-a` only pays for the shared label on `{u} ∪ C`.
The other factor is exactly the underlying tensor, up to inserting unit slots. -/
theorem SitePriceEval.diagonalControlBound_of_product {K : Type*} [Field K]
    {B C : Type} [Fintype B] [Fintype C] (p : SitePriceEval K B C)
    (hmul : p.BinaryProductAdditive) {E : ℝ} (hE : 0 ≤ E)
    (hdiag : ∀ (W : Type) [Fintype W] [Nonempty W],
      p.value (diagC (K := K) B C W) = E * Real.logb 2 (Fintype.card W)) :
    p.DiagonalControlBound E := by
  intro Tag U X Y _ _ _ _ _ T
  by_cases hz : T = 0
  · have leT : p.value (diagonalControl (Tag := Tag) T) ≤ p.value T := by
      apply p.mono
      refine ⟨fun _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0, ?_⟩
      funext u x y
      simp [Tensor.restrict, diagonalControl, hz]
    have hcard : (1 : ℝ) ≤ Fintype.card Tag := by exact_mod_cast Fintype.card_pos (α := Tag)
    exact leT.trans (le_add_of_nonneg_right (mul_nonneg hE (Real.logb_nonneg (by norm_num) hcard)))
  · let D := diagC (K := K) B C Tag
    have hre : p.value (diagonalControl (Tag := Tag) T) = p.value (SitePriceEval.splitProduct D T) := by
      apply p.value_reindex (Equiv.refl _) (fun b => (Equiv.uniqueProd (X b) Unit).symm)
        (fun _ => Equiv.refl _)
      intro u x y
      simp [D, SitePriceEval.splitProduct, diagonalControl, diagC, placeC, diagonalCoeff, ite_mul]
    rw [hre, hmul D T diagC_ne_zero hz, hdiag Tag, add_comm]

end

end SpectralBooks
end LinearAlgebra
end OAI

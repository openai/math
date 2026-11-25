import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Choose

/-! # Rank of tensors in a finitely generated span -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation

/-- A linear combination of a finite family of tensors of rank at most
`s` has rank at most `s` times the size of the family. -/
theorem rankAtMost_of_mem_span {F X Y Z I : Type*} [CommSemiring F] [Fintype I]
    (W : I → Tensor F X Y Z) {s : ℕ} (hW : ∀ i, (W i).RankAtMost s)
    {T : Tensor F X Y Z} (hT : T ∈ Submodule.span F (Set.range W)) :
    T.RankAtMost (Fintype.card I * s) := by
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hT
  choose a b c h using fun i => (hW i).scale (d i)
  let A (p : I × Fin s) := a p.1 p.2
  let B (p : I × Fin s) := b p.1 p.2
  let C (p : I × Fin s) := c p.1 p.2
  have heq : ∑ i, d i • W i = fun x y z =>
      ∑ p, Tensor.rankOne (A p) (B p) (C p) x y z := by
    funext x y z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun i _ => congrFun (congrFun (congrFun (h i) x) y) z)
  rw [heq]
  simpa using Tensor.rankAtMost_sum_rankOne A B C

end SpectralBooks
end LinearAlgebra
end OAI

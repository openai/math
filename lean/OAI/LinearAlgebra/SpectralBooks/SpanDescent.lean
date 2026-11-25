import OAI.LinearAlgebra.SpectralBooks.BorderRank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Descent of a linear span in a fixed tensor format

A linear retraction from the algebraic closure onto the ground field recovers
a ground-field expansion from a linear combination of scalar-extended tensors.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation

variable {F X Y Z I : Type*} [Field F] [Fintype I]

/-- A linear dependence expressing a ground tensor in the span of ground
tensors descends from the algebraic closure. -/
theorem mem_span_of_toAlgebraicClosure_mem_span (T : Tensor F X Y Z)
    (W : I → Tensor F X Y Z)
    (h : toAlgebraicClosure T ∈
      Submodule.span (AlgebraicClosure F) (Set.range (fun i => toAlgebraicClosure (W i)))) :
    T ∈ Submodule.span F (Set.range W) := by
  obtain ⟨l, hl⟩ := (Algebra.linearMap F (AlgebraicClosure F)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F (AlgebraicClosure F)).injective)
  have retract (t : F) : l (algebraMap F (AlgebraicClosure F) t) = t :=
    LinearMap.congr_fun hl t
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h
  refine (Submodule.mem_span_range_iff_exists_fun _).mpr ⟨fun i => l (a i), ?_⟩
  funext x y z
  have ha' := congrArg (fun S : Tensor (AlgebraicClosure F) X Y Z => S x y z) ha
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toAlgebraicClosure] at ha' ⊢
  obtain he := congrArg l ha'
  rw [map_sum, retract] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm (a i), ← Algebra.smul_def, l.map_smul]
  exact mul_comm _ _

end SpectralBooks
end LinearAlgebra
end OAI

import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Descent of span membership under scalar extension -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- If scalar extension expresses a ground-field function in the span of a finite
family of ground-field functions, an expansion already exists over the ground field. -/
theorem mem_span_of_map_mem_span {F E X J : Type*} [Field F] [Field E] [Algebra F E]
    [Fintype J] (x : X → F) (U : J → X → F)
    (h : (fun i => algebraMap F E (x i)) ∈
      Submodule.span E (Set.range (fun j i => algebraMap F E (U j i)))) :
    x ∈ Submodule.span F (Set.range U) := by
  obtain ⟨l, hl⟩ := (Algebra.linearMap F E).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F E).injective)
  have retract (t : F) : l (algebraMap F E t) = t := LinearMap.congr_fun hl t
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp h
  refine (Submodule.mem_span_range_iff_exists_fun F).mpr ⟨fun j => l (a j), ?_⟩
  funext i
  have hi := congrFun ha i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
  have hli := congrArg l hi
  rw [map_sum, retract] at hli
  convert hli using 1
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm (a j), ← Algebra.smul_def, l.map_smul]
  exact mul_comm _ _

end SpectralBooks
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.SpectralBooks.MinkowskiSupport
import OAI.LinearAlgebra.SpectralBooks.TriangleMeasure
import OAI.LinearAlgebra.SpectralBooks.RieszSplit
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.Compact

/-! # Uniform density from separation of finite Borel measures -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set MeasureTheory
open scoped CompactlySupported

section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

private theorem exists_measure_of_positiveLinearMap (P : C(X, ℝ) →ₚ[ℝ] ℝ) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ ∀ f : C(X, ℝ), ∫ x, f x ∂μ = P f := by
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f ↦ P f.toContinuousMap
      map_add' := fun f g ↦ P.map_add _ _
      map_smul' := fun c f ↦ P.map_smul _ _
      monotone' := fun _ _ h ↦ P.monotone h }
  refine ⟨RealRMK.rieszMeasure Λ, inferInstance, fun f ↦ ?_⟩
  let fc : C_c(X, ℝ) := ⟨f, HasCompactSupport.of_compactSpace _⟩
  exact RealRMK.integral_rieszMeasure Λ fc

/-- A family which determines finite Borel measures on a compact Hausdorff
space spans a uniformly dense subspace of the real continuous functions. -/
theorem dense_span_of_separates_measures (S : Set C(X, ℝ))
    (hsep : ∀ (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      (∀ f ∈ S, ∫ x, f x ∂μ = ∫ x, f x ∂ν) → μ = ν) :
    Dense (Submodule.span ℝ S : Set C(X, ℝ)) := by
  intro f
  by_contra hf
  let M := (Submodule.span ℝ S).topologicalClosure
  have hf' : f ∉ M := hf
  obtain ⟨L, c, hM, hfc⟩ := geometric_hahn_banach_closed_point M.convex
    (Submodule.isClosed_topologicalClosure _) hf'
  have hzero (g : C(X, ℝ)) (hg : g ∈ M) : L g = 0 := by
    by_contra h
    have hc := hM ((c / L g) • g) (M.smul_mem _ hg)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ h] at hc
    exact hc.false
  obtain ⟨P, N, hL⟩ := exists_positiveLinearMap_sub L
  obtain ⟨μ, hμ, hP⟩ := exists_measure_of_positiveLinearMap P
  obtain ⟨ν, hν, hN⟩ := exists_measure_of_positiveLinearMap N
  have heq := hsep μ ν fun g hg ↦ by
    rw [hP, hN]
    exact sub_eq_zero.mp ((hL g).symm.trans
      (hzero g ((Submodule.span ℝ S).le_topologicalClosure (Submodule.subset_span hg))))
  have hLf : L f = 0 := by rw [hL, ← hP, ← hN, heq, sub_self]
  have h0 := hM 0 M.zero_mem
  simp only [map_zero] at h0
  exact (h0.trans hfc).ne' hLf

section

open scoped RealInnerProductSpace Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Triangle support functions, including degenerate triangles, span a uniformly
dense subspace of the continuous functions on the unit sphere. -/
theorem dense_span_triangleSupports :
    Dense (Submodule.span ℝ (triangleSupports E) : Set C(Metric.sphere (0 : E) 1, ℝ)) := by
  apply dense_span_of_separates_measures
  intro μ ν _ _ h
  apply eq_of_triangle_integrals μ ν
  intro v w
  have htri := h _ ⟨0, v, w, rfl⟩
  simpa only [sphereSupport, ContinuousMap.coe_mk, support,
    Finset.sup'_insert (Finset.insert_nonempty _ _), Finset.sup'_insert (Finset.singleton_nonempty _),
    Finset.sup'_singleton, inner_zero_right, max_assoc] using htri

end

end

end SpectralBooks
end LinearAlgebra
end OAI

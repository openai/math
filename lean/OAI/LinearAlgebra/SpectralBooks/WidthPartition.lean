import OAI.LinearAlgebra.SpectralBooks.Width
import OAI.LinearAlgebra.SpectralBooks.GaussianTies

/-! # Splitting mean width over the maximizing sites

The normal cones cover all directions and have Gaussian-null pairwise overlaps.
This yields the sum of the marginal integrals at the end of the flat diagonal law.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace Classical

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Translate the sites so that the specified vertex is the origin. -/
def centeredSites (S : Finset E) (v : E) : Finset E := S.image (· - v)

theorem mem_normalConeAtZero_centeredSites (S : Finset E) (v u : E) :
    u ∈ normalConeAtZero (centeredSites S v) ↔ ∀ w ∈ S, ⟪u, w⟫ ≤ ⟪u, v⟫ := by
  simp [normalConeAtZero, centeredSites, inner_sub_right]

theorem sum_normalCone_indicators {S : Finset E} (h0 : 0 ∈ S) (u : E)
    (htie : ∀ x ∈ S, ∀ y ∈ S, ⟪u, x⟫ = ⟪u, y⟫ → x = y) :
    ∑ v ∈ S, (normalConeAtZero (centeredSites S v)).indicator (fun g ↦ max ⟪g, v⟫ 0) u =
      support S ⟨0, h0⟩ u := by
  obtain ⟨v, hv, hmax⟩ := Finset.exists_mem_eq_sup' (s := S) ⟨0, h0⟩ (fun x ↦ ⟪u, x⟫)
  change support S ⟨0, h0⟩ u = ⟪u, v⟫ at hmax
  have hu : ∀ w ∈ S, ⟪u, w⟫ ≤ ⟪u, v⟫ := fun w hw ↦
    (S.le_sup' (fun x ↦ ⟪u, x⟫) hw).trans_eq hmax
  rw [Finset.sum_eq_single_of_mem v hv]
  · rw [Set.indicator_of_mem ((mem_normalConeAtZero_centeredSites S v u).mpr hu)]
    exact (max_eq_left ((support_nonneg_of_zero_mem h0 u).trans_eq hmax)).trans hmax.symm
  · intro w hw hne
    apply Set.indicator_of_notMem
    intro h
    have hle := (mem_normalConeAtZero_centeredSites S w u).mp h v hv
    exact hne (htie w hw v hv (le_antisymm (hu w hw) hle))

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Summing over all original sites gives the width exactly when the origin is
among the sites. The Gaussian hyperplanes on which the maximizer ties are null. -/
theorem sum_normalCone_marginals {S : Finset E} (h0 : 0 ∈ S) :
    ∑ v ∈ S, Real.sqrt (2 * Real.pi) *
      ∫ u in normalConeAtZero (centeredSites S v), max ⟪u, v⟫ 0 ∂stdGaussian E =
      meanWidth S ⟨0, h0⟩ := by
  rw [← Finset.mul_sum]
  unfold meanWidth
  congr 1
  simp_rw [← integral_indicator (measurableSet_normalConeAtZero _)]
  rw [← integral_finsetSum]
  · exact integral_congr_ae ((ae_no_ties S).mono fun u hu ↦ sum_normalCone_indicators h0 u hu)
  · intro v _
    exact ((IsGaussian.integrable_fun_id (μ := stdGaussian E)).inner_const (𝕜 := ℝ) v |>.sup
      (integrable_const 0)).indicator (measurableSet_normalConeAtZero _)

end

end

end SpectralBooks
end LinearAlgebra
end OAI

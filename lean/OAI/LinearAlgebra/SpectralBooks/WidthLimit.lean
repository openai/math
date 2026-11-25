import OAI.LinearAlgebra.SpectralBooks.Width

/-! # Continuity of Gaussian mean width for finite configurations -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace Classical

section

variable {A E : Type*} [Fintype A] [Nonempty A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Mean width converges when each site of a fixed finite configuration converges.
The limiting configuration may have coincident sites. -/
theorem tendsto_meanWidth_image [DecidableEq E] {f : ℕ → A → E} {g : A → E}
    (hf : ∀ i, Tendsto (fun n ↦ f n i) atTop (𝓝 (g i))) :
    Tendsto (fun n ↦ meanWidth (Finset.univ.image (f n)) (Finset.univ_nonempty.image _))
      atTop (𝓝 (meanWidth (Finset.univ.image g) (Finset.univ_nonempty.image _))) := by
  let R := Finset.univ.sup' Finset.univ_nonempty fun i ↦ ‖g i‖ + 1
  have hR : ∀ᶠ n in atTop, ∀ i, ‖f n i‖ ≤ R := by
    apply eventually_all.mpr
    intro i
    have hi : ‖g i‖ < ‖g i‖ + 1 := lt_add_one _
    filter_upwards [(hf i).norm.eventually_lt_const hi] with n hn
    exact hn.le.trans (Finset.le_sup' (fun j ↦ ‖g j‖ + 1) (Finset.mem_univ i))
  unfold meanWidth
  apply tendsto_const_nhds.mul
  apply tendsto_integral_filter_of_dominated_convergence (fun u : E ↦ ‖u‖ * R)
  · exact .of_forall fun n ↦ (integrable_support _ _).aestronglyMeasurable
  · filter_upwards [hR] with n hn
    refine ae_of_all _ fun u ↦ ?_
    simp only [support, Finset.sup'_image, Function.comp_apply]
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i ↦ ⟪u, f n i⟫)
    rw [hi]
    exact (norm_inner_le_norm u (f n i)).trans (mul_le_mul_of_nonneg_left (hn i) (norm_nonneg u))
  · exact (IsGaussian.integrable_fun_id (μ := stdGaussian E)).norm.mul_const R
  · refine ae_of_all _ fun u ↦ ?_
    simp only [support, Finset.sup'_image, Function.comp_apply]
    exact Tendsto.finset_sup'_nhds_apply Finset.univ_nonempty
      fun i _ ↦ tendsto_const_nhds.inner (hf i)

end

end SpectralBooks
end LinearAlgebra
end OAI

import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Lattice

/-!
# Approximation of the support of the spine ball

Finite subsets of the closed unit ball containing its center approximate its
support function pointwise. This is the geometric limit in the proof of
Theorem `thm:student`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Metric Set
open scoped InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The support function of a finite spine configuration together with its center. -/
noncomputable def spineSupport (B : Finset E) (g : E) : ℝ := by
  classical
  exact (insert 0 B).sup' (Finset.insert_nonempty _ _) (fun x => ⟪g, x⟫_ℝ)

theorem spineSupport_nonneg (B : Finset E) (g : E) : 0 ≤ spineSupport B g := by
  classical
  simpa only [spineSupport, inner_zero_right] using
    (Finset.le_sup' (fun x => ⟪g, x⟫_ℝ) (Finset.mem_insert_self 0 B))

theorem inner_le_spineSupport {B : Finset E} {x : E} (hx : x ∈ B) (g : E) :
    ⟪g, x⟫_ℝ ≤ spineSupport B g := by
  classical
  exact Finset.le_sup' _ (Finset.mem_insert_of_mem hx)

theorem spineSupport_le_norm {B : Finset E} (hB : ∀ x ∈ B, ‖x‖ ≤ 1) (g : E) :
    spineSupport B g ≤ ‖g‖ := by
  classical
  apply Finset.sup'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · simp
  · exact (real_inner_le_norm _ _).trans
      (by simpa using mul_le_mul_of_nonneg_left (hB _ hx) (norm_nonneg g))

theorem continuous_spineSupport (B : Finset E) : Continuous (spineSupport B) := by
  classical
  exact Continuous.finset_sup'_apply (Finset.insert_nonempty _ _)
    (fun x _ => continuous_id.inner (continuous_const (y := x)))

/-- An internal finite net for the closed unit ball, including the origin. -/
theorem exists_spine_net (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ε : ℝ} (hε : 0 < ε) :
    ∃ B : Finset E, 0 ∈ B ∧ (∀ x ∈ B, ‖x‖ ≤ 1) ∧
      ∀ y : E, ‖y‖ ≤ 1 → ∃ x ∈ B, ‖y - x‖ < ε := by
  classical
  obtain ⟨s, hs, hfin, hcover⟩ := (isCompact_closedBall (0 : E) 1).finite_cover_balls hε
  refine ⟨insert 0 hfin.toFinset, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp
    · simpa using hs (hfin.mem_toFinset.mp hx)
  · intro y hy
    have hmem := hcover (show y ∈ closedBall 0 1 by simpa using hy)
    obtain ⟨x, hx, hxy⟩ := by simpa only [mem_iUnion, exists_prop] using hmem
    exact ⟨x, Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hx), by
      simpa only [mem_ball, dist_eq_norm] using hxy⟩

/-- The support error of a finite net is at most its mesh times the norm of
the test vector. -/
theorem norm_sub_mesh_le_spineSupport {B : Finset E} {ε : ℝ}
    (hnet : ∀ y : E, ‖y‖ ≤ 1 → ∃ x ∈ B, ‖y - x‖ < ε) (g : E) :
    ‖g‖ - ‖g‖ * ε ≤ spineSupport B g := by
  by_cases hg : g = 0
  · simpa [hg] using spineSupport_nonneg B (0 : E)
  have hunit := NormedSpace.norm_normalize hg
  obtain ⟨x, hx, hdist⟩ := hnet _ hunit.le
  have hinner : ⟪g, NormedSpace.normalize g⟫_ℝ = ‖g‖ := by
    rw [NormedSpace.normalize, real_inner_smul_right, real_inner_self_eq_norm_mul_norm,
      inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr hg)]
  have hCS := (real_inner_le_norm g (NormedSpace.normalize g - x)).trans
    (mul_le_mul_of_nonneg_left hdist.le (norm_nonneg g))
  rw [inner_sub_right, hinner] at hCS
  exact (sub_le_comm.mp hCS).trans (inner_le_spineSupport hx g)

/-- The finite configurations in the proof of the spine-ball inequality. -/
theorem exists_spineSupport_net (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ B : ℕ → Finset E, (∀ n, 0 ∈ B n) ∧ (∀ n x, x ∈ B n → ‖x‖ ≤ 1) ∧
      ∀ g, Tendsto (fun n => spineSupport (B n) g) atTop (𝓝 ‖g‖) := by
  choose B hzero hB hnet using fun n : ℕ =>
    exists_spine_net E (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  refine ⟨B, hzero, hB, fun g => ?_⟩
  have ht : Tendsto (fun n : ℕ => ‖g‖ - ‖g‖ * (1 / ((n : ℝ) + 1))) atTop (𝓝 ‖g‖) := by
    simpa using tendsto_const_nhds.sub
      ((tendsto_const_nhds (x := ‖g‖)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le ht tendsto_const_nhds
    (fun n => norm_sub_mesh_le_spineSupport (hnet n) g) (fun n => spineSupport_le_norm (hB n) g)

end SpectralBooks
end LinearAlgebra
end OAI

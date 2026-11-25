import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.Normed.Module.Connected
import OAI.Computability.BorderVNP.ShortenEpochBisectors
import OAI.Computability.BorderVNP.CoverLorentzPlaneTile

/-!
# Linear boundary-strip bound on the arithmetic host

The Dirichlet polygon for the arithmetic congruence subgroup has a compact
frontier on finitely many hyperbolic bisectors. The unit-speed side covers
below yield a single constant for all small rounding radii, computed with
the invariant area measure of the actual upper half-plane.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open UpperHalfPlane Real Set Metric MeasureTheory

/-- The radius-`r` strip around the frontier of a set of lifted positions. -/
def tileStrip (tile : Set UpperHalfPlane) (r : ℝ) : Set UpperHalfPlane :=
  {z | ∃ w ∈ frontier tile, dist z w ≤ r}

/-- The radius-`r` boundary strip of the level-`l` closed Dirichlet tile. -/
def dirichletStrip (l : ℕ) := tileStrip (Cover.dirichlet l)

private theorem arithmetic_strip_area (l : ℕ) (tile : Set UpperHalfPlane)
    (ht : tile ⊆ Cover.dirichlet (l+1))
    (hboundary : ∃ s : Finset (Cover.gamma (l+1)), (∀ u ∈ s, u ≠ 1) ∧
      ∀ z ∈ frontier tile, ∃ u ∈ s, dist z I = dist z (Cover.gammaSL (l+1) u • I)) :
    ∃ C ≥ (0 : ℝ), ∀ r > (0 : ℝ), 2*r ≤ 1 → volume (tileStrip tile r) ≤ ENNReal.ofReal (C*r) := by
  classical
  obtain ⟨s,hn,hcover⟩ := hboundary
  let K := Cover.dirichlet (l+1)
  have hK : IsCompact K := Cover.dirichlet_compact _
  have hline (u : s) :
      ∃ L ≥ (0 : ℝ), ∃ γ : ℝ → UpperHalfPlane, Isometry γ ∧
      ∀ z ∈ K, dist z I = dist z (Cover.gammaSL (l+1) u.val • I) →
        ∃ t ∈ Icc (0 : ℝ) L, γ t = z := by
    have hsite : Cover.gammaSL (l+1) u.val • I ≠ I := fun he =>
      hn u.val u.property (Cover.eq_one_of_fix _ _ he)
    rcases Cover.bisector_line_or_circle hsite with ⟨a,ha⟩ | ⟨a,R,hR,ha⟩
    · obtain ⟨L,hL,γ,hi,h⟩ := vertical_bounded_arc hK a
      exact ⟨L,hL,γ,hi,fun z hz he => h z hz (ha z he)⟩
    · obtain ⟨L,hL,γ,hi,h⟩ := semicircle_bounded_arc hK a R hR
      exact ⟨L,hL,γ,hi,fun z hz he => h z hz (ha z he)⟩
  choose L hL γ hγ hline using hline
  refine ⟨∑ u, 4 * (exp 1 * cosh 1)^2 * Real.pi * (L u+1), ?_, ?_⟩
  · apply Finset.sum_nonneg
    intro u _
    have := hL u
    positivity
  · intro r hr hr1
    apply le_trans (measure_mono ?_) (polygonStrip_area_le γ L (fun u => (hγ u).lipschitzWith) hL hr hr1)
    rintro z ⟨w, hw, hzw⟩
    have hwK : w ∈ K := closure_minimal ht hK.isClosed hw.1
    obtain ⟨u,hu,hwu⟩ := hcover w hw
    obtain ⟨t,ht,he⟩ := hline ⟨u,hu⟩ w hwK hwu
    exact mem_iUnion.mpr ⟨⟨u,hu⟩, t,ht,by simpa only [he] using hzw⟩

/-- Uniform linear area bound for the closed tile. -/
theorem dirichletStrip_area_le (l : ℕ) : ∃ C ≥ (0 : ℝ), ∀ r > (0 : ℝ), 2*r ≤ 1 →
    volume (dirichletStrip (l+1) r) ≤ ENNReal.ofReal (C*r) :=
  arithmetic_strip_area l _ Subset.rfl (Cover.dirichlet_frontier_bisectors l)

/-- Uniform linear area bound on the frontier of the actual tie-resolved Borel tile. -/
theorem planeTileStrip_area_le (l : ℕ) : ∃ C ≥ (0 : ℝ), ∀ r > (0 : ℝ), 2*r ≤ 1 →
    volume (tileStrip (Cover.planeTile l) r) ≤ ENNReal.ofReal (C*r) :=
  arithmetic_strip_area l _ (fun _ hz => hz.1) (Cover.planeTile_frontier_bisectors l)

/-- Any endpoint starting in a tile and leaving its interior is within the
length of the segment of the tile frontier. This works for arbitrary seam conventions. -/
theorem mem_tileStrip_of_leaving {K : Set UpperHalfPlane} {z w : UpperHalfPlane} {r : ℝ}
    (hz : z ∈ K) (hw : w ∉ interior K) (hd : dist z w ≤ r) : z ∈ tileStrip K r := by
  let S := closedBall z r
  have hcon : IsPreconnected S := by
    rw [← UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image,
      UpperHalfPlane.image_coe_closedBall]
    exact isPreconnected_closedBall
  have hzS : z ∈ S := mem_closedBall_self (dist_nonneg.trans hd)
  have hwS : w ∈ S := by simpa only [S, mem_closedBall, dist_comm w z] using hd
  by_contra! h
  have hsub : S ⊆ interior K ∪ interior Kᶜ := by
    rw [← compl_frontier_eq_union_interior]
    intro x hx hxf
    exact h ⟨x,hxf,by simpa only [S, mem_closedBall, dist_comm x z] using hx⟩
  have hdis : Disjoint (interior K) (interior Kᶜ) :=
    disjoint_compl_right.mono interior_subset interior_subset
  rcases hcon.subset_or_subset isOpen_interior isOpen_interior hdis hsub with h | h
  · exact hw (h hwS)
  · exact (interior_subset (h hzS)) hz

/-- The area of starting points on the base polygon for a move of length
at most `r` leaving the tile is bounded by a constant times `r`. -/
theorem dirichlet_rounding_area (l : ℕ) : ∃ C ≥ (0 : ℝ), ∀ r > (0 : ℝ), 2*r ≤ 1 →
    ∀ (endpoint : UpperHalfPlane → UpperHalfPlane),
      (∀ z ∈ Cover.dirichlet (l+1), dist z (endpoint z) ≤ r) →
      volume {z | z ∈ Cover.dirichlet (l+1) ∧ endpoint z ∉ interior (Cover.dirichlet (l+1))} ≤
        ENNReal.ofReal (C*r) := by
  obtain ⟨C,hC,h⟩ := dirichletStrip_area_le l
  refine ⟨C,hC,fun r hr hr1 e he => (measure_mono ?_).trans (h r hr hr1)⟩
  intro z hz
  exact mem_tileStrip_of_leaving hz.1 hz.2 (he z hz.1)

open Filter
open scoped Topology

private theorem null_frontier_of_strip {K : Set UpperHalfPlane} {C : ℝ}
    (h : ∀ r > (0 : ℝ), 2*r ≤ 1 → volume (tileStrip K r) ≤ ENNReal.ofReal (C*r)) :
    volume (frontier K) = 0 := by
  have ht : Tendsto (fun r : ℝ => ENNReal.ofReal (C*r)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_nhdsWithin_of_tendsto_nhds
      (continuousAt_const.mul continuousAt_id : ContinuousAt (fun r : ℝ => C*r) 0))
  apply le_antisymm _ bot_le
  apply ge_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1/2 by norm_num)] with r hr
  apply le_trans (measure_mono ?_) (h r hr.1 (by linarith only [hr.2]))
  exact fun z hz => ⟨z,hz,by simpa using hr.1.le⟩

/-- The seams of the closed Dirichlet tile are null for hyperbolic area. -/
theorem dirichlet_frontier_null (l : ℕ) : volume (frontier (Cover.dirichlet (l+1))) = 0 := by
  obtain ⟨_,_,h⟩ := dirichletStrip_area_le l
  exact null_frontier_of_strip h

/-- The seams of the actual tie-resolved tile are null for hyperbolic area. -/
theorem planeTile_frontier_null (l : ℕ) : volume (frontier (Cover.planeTile l)) = 0 := by
  obtain ⟨_,_,h⟩ := planeTileStrip_area_le l
  exact null_frontier_of_strip h

private theorem rounding_test_of_strip {K : Set UpperHalfPlane} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ r > (0 : ℝ), 2*r ≤ 1 → volume (tileStrip K r) ≤ ENNReal.ofReal (C*r)) :
    ∃ A ≥ (0 : ℝ), ∀ r > (0 : ℝ), 4*r ≤ 1 →
    ∃ S : Set UpperHalfPlane, IsOpen S ∧ volume (frontier S) = 0 ∧ volume S ≤ ENNReal.ofReal (A*r) ∧
      ∀ z ∈ K, ∀ w, w ∉ interior K → dist z w ≤ r → z ∈ S := by
  refine ⟨2*C, by positivity, ?_⟩
  intro r hr hr1
  obtain ⟨ρ,hρ,hn⟩ := exists_null_frontier_thickening volume (frontier K)
    (show r < 2*r by linarith)
  refine ⟨thickening ρ (frontier K), isOpen_thickening, hn, ?_, ?_⟩
  · have hsub : thickening ρ (frontier K) ⊆ tileStrip K (2*r) := by
      intro z hz
      obtain ⟨w,hw,he⟩ := mem_thickening_iff.mp hz
      exact ⟨w,hw,(he.trans hρ.2).le⟩
    convert (measure_mono hsub).trans (h (2*r) (by positivity) (by linarith)) using 1
    congr 1
    ring
  · intro z hz w hw hd
    obtain ⟨a,ha,hza⟩ := mem_tileStrip_of_leaving hz hw hd
    exact mem_thickening_iff.mpr ⟨a,ha,hza.trans_lt hρ.1⟩

/-- Open null-frontier test bounding every failure of rounding on the actual
Borel tile, with linear area and a constant independent of the segment lengths. -/
theorem exists_planeTile_rounding_test (l : ℕ) : ∃ C ≥ (0 : ℝ), ∀ r > (0 : ℝ), 4*r ≤ 1 →
    ∃ S : Set UpperHalfPlane, IsOpen S ∧ volume (frontier S) = 0 ∧ volume S ≤ ENNReal.ofReal (C*r) ∧
      ∀ z ∈ Cover.planeTile l, ∀ w, w ∉ interior (Cover.planeTile l) → dist z w ≤ r → z ∈ S := by
  obtain ⟨C,hC,h⟩ := planeTileStrip_area_le l
  exact rounding_test_of_strip hC h

end Epoch

end BorderVNP
end Computability
end OAI

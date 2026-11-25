import OAI.LinearAlgebra.SpectralBooks.BookCAT0

/-! # Finite approximations to the doubled coordinate cube

At every mesh size one can retain the center and all the doubled corners.
Chosen grid approximations of cube points converge as the mesh goes to zero.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Set Metric
open scoped Topology

section

variable {ι : Type*} [Fintype ι]

private theorem exists_cubeGrid (ι : Type*) [Fintype ι] (n : ℕ) :
    ∃ s : Finset (EuclideanSpace ℝ ι),
      (s : Set _) ⊆ coordinateCube ι 2 ∧ 0 ∈ s ∧
      (∀ z ∈ coordinateCubeCorners ι 1, (2 : ℝ) • z ∈ s) ∧
      ∀ x ∈ coordinateCube ι 2, ∃ y ∈ s, dist x y < 1 / ((n : ℝ) + 1) := by
  classical
  obtain ⟨t, hsub, hfin, hcov⟩ :=
    (isCompact_coordinateCube (ι := ι) 2).finite_cover_balls
      (show 0 < 1 / ((n : ℝ) + 1) by positivity)
  let corners := (coordinateCubeCorners ι 1).image (fun z ↦ (2 : ℝ) • z)
  have hcsub : (coordinateCubeCorners ι 1 : Set _) ⊆ coordinateCube ι 1 := by
    rw [← convexHull_coordinateCubeCorners (by norm_num : 0 ≤ (1 : ℝ))]
    exact subset_convexHull _ _
  refine ⟨insert 0 (corners ∪ hfin.toFinset), ?_, Finset.mem_insert_self .., ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | h
    · intro i
      norm_num
    rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_image.mp h with ⟨z, hz, rfl⟩
      intro i
      have hi := hcsub hz i
      change -2 ≤ 2 * z i ∧ 2 * z i ≤ 2
      constructor <;> linarith [hi.1, hi.2]
    · exact hsub (hfin.mem_toFinset.mp h)
  · intro z hz
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hz))
  · intro x hx
    obtain ⟨y, hy, he⟩ := mem_iUnion₂.mp (hcov hx)
    exact ⟨y, Finset.mem_insert_of_mem (Finset.mem_union_right _ (hfin.mem_toFinset.mpr hy)), he⟩

/-- A finite mesh of the doubled coordinate cube, including its center and doubled corners. -/
noncomputable def cubeGrid (ι : Type*) [Fintype ι] (n : ℕ) : Finset (EuclideanSpace ℝ ι) :=
  (exists_cubeGrid ι n).choose

theorem cubeGrid_subset (ι : Type*) [Fintype ι] (n : ℕ) :
    (cubeGrid ι n : Set _) ⊆ coordinateCube ι 2 :=
  (exists_cubeGrid ι n).choose_spec.1

theorem zero_mem_cubeGrid (ι : Type*) [Fintype ι] (n : ℕ) :
    0 ∈ cubeGrid ι n :=
  (exists_cubeGrid ι n).choose_spec.2.1

theorem double_corner_mem_cubeGrid (n : ℕ) {z : EuclideanSpace ℝ ι}
    (hz : z ∈ coordinateCubeCorners ι 1) : (2 : ℝ) • z ∈ cubeGrid ι n :=
  (exists_cubeGrid ι n).choose_spec.2.2.1 z hz

private theorem exists_gridPoint (n : ℕ) {x : EuclideanSpace ℝ ι}
    (hx : x ∈ coordinateCube ι 2) :
    ∃ y ∈ cubeGrid ι n, dist x y < 1 / ((n : ℝ) + 1) :=
  (exists_cubeGrid ι n).choose_spec.2.2.2 x hx

/-- Choose a nearby grid point for each point of the cube, fixing all grid points. -/
noncomputable def gridPoint (n : ℕ) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι := by
  classical
  exact if x ∈ cubeGrid ι n then x else
    if hx : x ∈ coordinateCube ι 2 then (exists_gridPoint n hx).choose else 0

theorem gridPoint_eq_of_mem {n : ℕ} {x : EuclideanSpace ℝ ι}
    (hx : x ∈ cubeGrid ι n) : gridPoint n x = x := by
  classical
  simp [gridPoint, hx]

theorem gridPoint_mem (n : ℕ) (x : EuclideanSpace ℝ ι) :
    gridPoint n x ∈ cubeGrid ι n := by
  classical
  by_cases hx : x ∈ cubeGrid ι n
  · rwa [gridPoint_eq_of_mem hx]
  by_cases hc : x ∈ coordinateCube ι 2
  · simpa [gridPoint, hx, hc] using (exists_gridPoint n hc).choose_spec.1
  · simpa [gridPoint, hx, hc] using zero_mem_cubeGrid ι n

theorem dist_gridPoint_lt (n : ℕ) {x : EuclideanSpace ℝ ι} (hx : x ∈ coordinateCube ι 2) :
    dist (gridPoint n x) x < 1 / ((n : ℝ) + 1) := by
  classical
  by_cases h : x ∈ cubeGrid ι n
  · rw [gridPoint_eq_of_mem h, dist_self]
    positivity
  · simpa [dist_comm x, gridPoint, h, hx] using (exists_gridPoint n hx).choose_spec.2

theorem tendsto_gridPoint {x : EuclideanSpace ℝ ι} (hx : x ∈ coordinateCube ι 2) :
    Tendsto (fun n ↦ gridPoint n x) atTop (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hε
  exact h.mono fun n hn ↦ (dist_gridPoint_lt n hx).trans hn

end

end SpectralBooks
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.SpectralBooks.GridPlacement
import OAI.LinearAlgebra.SpectralBooks.BookCubePrices

/-! # Mean widths of the finite doubled-grid placements

In each active grid, the corner labels attain all vertices of the unit cube,
and the remaining labels stay inside their convex hull. In an inactive grid
every label is placed at zero.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open Set
open scoped Classical

section

variable (ι : Type*) [Fintype ι]

/-- Center and private labels of a grid in the finite doubling construction. -/
def gridLabels (n : ℕ) (k : Bool) : Finset (DoubledGridSite ι n) :=
  Finset.univ.image (gridLabel k)

/-- The common center and the corner labels of a single grid. -/
def cornerLabels (n : ℕ) (k : Bool) : Finset (DoubledGridSite ι n) :=
  insert gridCenter (Finset.univ.image (fun z : coordinateCubeCorners ι 1 ↦
    gridLabel k ⟨(2 : ℝ) • z.val, double_corner_mem_cubeGrid n z.property⟩))

theorem cornerLabels_nonempty (n : ℕ) (k : Bool) : (cornerLabels ι n k).Nonempty :=
  Finset.insert_nonempty _ _

theorem cornerLabels_subset_gridLabels (n : ℕ) (k : Bool) :
    cornerLabels ι n k ⊆ gridLabels ι n k := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | h
  · exact Finset.mem_image.mpr ⟨⟨0, zero_mem_cubeGrid ι n⟩, Finset.mem_univ _, by simp [gridLabel]⟩
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp h
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem gridLabels_nonempty (n : ℕ) (k : Bool) : (gridLabels ι n k).Nonempty :=
  (cornerLabels_nonempty ι n k).mono (cornerLabels_subset_gridLabels ι n k)

private theorem gridPlacement_grid_mem (n : ℕ) (page : Option Bool) (k : Bool)
    {s : DoubledGridSite ι n} (hs : s ∈ gridLabels ι n k) :
    gridPlacement page s ∈ coordinateCube ι 1 := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hs
  rw [gridPlacement_gridLabel]
  split
  · intro j
    have hj := cubeGrid_subset ι n x.property j
    change -1 ≤ 1 / 2 * (x.val j) ∧ 1 / 2 * (x.val j) ≤ 1
    constructor <;> linarith [hj.1, hj.2]
  · intro j
    norm_num

private theorem corners_subset_placed (n : ℕ) {page : Option Bool} {k : Bool}
    (hpage : page = none ∨ page = some k) :
    coordinateCubeCorners ι 1 ⊆ (cornerLabels ι n k).image (gridPlacement page) := by
  intro z hz
  let x : cubeGrid ι n := ⟨(2 : ℝ) • z, double_corner_mem_cubeGrid n hz⟩
  refine Finset.mem_image.mpr ⟨gridLabel k x, ?_, ?_⟩
  · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_univ _, rfl⟩)
  · simp [x, hpage, smul_smul]

private theorem placed_width_of_corners_subset (n : ℕ) (page : Option Bool)
    (S : Finset (DoubledGridSite ι n)) (hS : S.Nonempty)
    (hc : coordinateCubeCorners ι 1 ⊆ S.image (gridPlacement page))
    (hs : ∀ s ∈ S, gridPlacement page s ∈ coordinateCube ι 1) :
    meanWidth (S.image (gridPlacement page)) (hS.image _) = innerCubeWidth ι := by
  classical
  have ht : ((S.image (gridPlacement page)) : Set _) ⊆
      convexHull ℝ (coordinateCubeCorners ι 1 : Set (EuclideanSpace ℝ ι)) := by
    rw [convexHull_coordinateCubeCorners (by norm_num : 0 ≤ (1 : ℝ))]
    intro x hx
    obtain ⟨s, h, rfl⟩ := Finset.mem_image.mp hx
    exact hs s h
  have he := meanWidth_union_of_subset_convexHull (coordinateCubeCorners_nonempty ι 1) ht
  convert! he using 1
  congr 1
  have eq := (Finset.union_eq_right.mpr hc).symm
  convert! eq using 1
  congr! 3

private theorem meanWidth_grid_subset (n : ℕ) (page : Option Bool) (k : Bool)
    (S : Finset (DoubledGridSite ι n)) (hS : S.Nonempty)
    (hcorner : cornerLabels ι n k ⊆ S) (hgrid : S ⊆ gridLabels ι n k) :
    meanWidth (S.image (gridPlacement page)) (hS.image _) =
      if page = none ∨ page = some k then innerCubeWidth ι else 0 := by
  split
  next h =>
    exact placed_width_of_corners_subset ι n page S hS
      ((corners_subset_placed ι n h).trans (Finset.image_mono _ hcorner))
      (fun _ hs ↦ gridPlacement_grid_mem ι n page k (hgrid hs))
  next h =>
    have he : S.image (gridPlacement page) = {0} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      have hz : ∀ s ∈ S, gridPlacement page s = 0 := by
        intro s hs
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp (hgrid hs)
        simp [h]
      obtain ⟨s, hs⟩ := hS
      refine ⟨Finset.mem_image.mpr ⟨s, hs, hz s hs⟩, ?_⟩
      intro y hy
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
      exact hz t ht
    simp [he, meanWidth, support]

theorem meanWidth_gridLabels (n : ℕ) (page : Option Bool) (k : Bool) :
    meanWidth ((gridLabels ι n k).image (gridPlacement page)) ((gridLabels_nonempty ι n k).image _) =
      if page = none ∨ page = some k then innerCubeWidth ι else 0 :=
  meanWidth_grid_subset ι n page k _ (gridLabels_nonempty ι n k) (cornerLabels_subset_gridLabels ι n k) Finset.Subset.rfl

theorem meanWidth_cornerLabels (n : ℕ) (page : Option Bool) (k : Bool) :
    meanWidth ((cornerLabels ι n k).image (gridPlacement page)) ((cornerLabels_nonempty ι n k).image _) =
      if page = none ∨ page = some k then innerCubeWidth ι else 0 :=
  meanWidth_grid_subset ι n page k _ (cornerLabels_nonempty ι n k) Finset.Subset.rfl (cornerLabels_subset_gridLabels ι n k)

theorem meanWidth_gridLabels_union (n : ℕ) (page : Option Bool) :
    meanWidth ((gridLabels ι n false ∪ gridLabels ι n true).image (gridPlacement page))
      (((gridLabels_nonempty ι n false).mono Finset.subset_union_left).image _) = innerCubeWidth ι := by
  refine placed_width_of_corners_subset ι n page (gridLabels ι n false ∪ gridLabels ι n true) ((gridLabels_nonempty ι n false).mono Finset.subset_union_left) ?_ ?_
  · obtain ⟨k, hk⟩ : ∃ k, page = none ∨ page = some k := by cases page <;> simp
    apply (corners_subset_placed ι n hk).trans
    apply Finset.image_mono
    apply (cornerLabels_subset_gridLabels ι n k).trans
    cases k
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  · intro s hs
    rcases Finset.mem_union.mp hs with h | h
    · exact gridPlacement_grid_mem ι n page false h
    · exact gridPlacement_grid_mem ι n page true h

end

end

end SpectralBooks
end LinearAlgebra
end OAI

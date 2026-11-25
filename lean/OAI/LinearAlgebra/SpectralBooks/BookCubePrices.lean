import OAI.LinearAlgebra.SpectralBooks.BookCAT0
import OAI.LinearAlgebra.SpectralBooks.BookIndependence
import OAI.LinearAlgebra.SpectralBooks.MinkowskiSupport

/-!
# Diagonal independence for the finite sites of two doubled cubes

The flat law on each doubled cube determines its diagonal price even after
inner corners and arbitrary sites of the cube have been adjoined. Together
with the joint corner price these facts imply equation `eq:book-independence`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open Set
open scoped RealInnerProductSpace Classical

section

variable {ι : Type*} [Fintype ι]

theorem mem_coordinateCubeCorners_iff {a : ℝ} {x : EuclideanSpace ℝ ι} :
    x ∈ coordinateCubeCorners ι a ↔ ∀ j, x j = -a ∨ x j = a := by
  rw [coordinateCubeCorners, Finset.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩ j
    simpa using (Fintype.mem_piFinset.mp hy j)
  · intro h
    refine ⟨WithLp.ofLp x, Fintype.mem_piFinset.mpr (fun j ↦ ?_), rfl⟩
    simpa using h j

theorem coordinateCubeCorners_nonempty (ι : Type*) [Fintype ι] (a : ℝ) :
    (coordinateCubeCorners ι a).Nonempty :=
  ⟨WithLp.toLp 2 (fun _ ↦ a), mem_coordinateCubeCorners_iff.mpr (fun _ ↦ Or.inr rfl)⟩

theorem doubled_cube_corners :
    coordinateCubeCorners ι 2 = (coordinateCubeCorners ι 1).image ((2 : ℝ) • ·) := by
  ext x
  rw [mem_coordinateCubeCorners_iff, Finset.mem_image]
  constructor
  · intro hx
    refine ⟨(1 / 2 : ℝ) • x, mem_coordinateCubeCorners_iff.mpr (fun j ↦ ?_), ?_⟩
    · rcases hx j with h | h <;> simp [PiLp.smul_apply, h]
    · rw [smul_smul]; norm_num
  · rintro ⟨v, hv, rfl⟩ j
    rcases mem_coordinateCubeCorners_iff.mp hv j with h | h <;> simp [PiLp.smul_apply, h]

/-- The number designated by `D` in the cube construction. -/
def innerCubeWidth (ι : Type*) [Fintype ι] : ℝ :=
  meanWidth (coordinateCubeCorners ι 1) (coordinateCubeCorners_nonempty ι 1)

theorem meanWidth_doubled_cube_corners :
    meanWidth (coordinateCubeCorners ι 2) (coordinateCubeCorners_nonempty ι 2) =
      2 * innerCubeWidth ι := by
  simp only [doubled_cube_corners, innerCubeWidth]
  convert! (meanWidth_smul (coordinateCubeCorners ι 1) (coordinateCubeCorners_nonempty ι 1)
      (show (0 : ℝ) ≤ 2 by norm_num)) using 1
  congr! 3

variable {X : Type*} [DecidableEq X] {δ : Finset X → ℝ}

/-- In the two doubled cube charts, the flat law and the joint price on the
outer corners imply independence for all finite choices of sites. -/
theorem doubled_cube_diagonal_independence (hs : IntersectingSubmodular δ)
    (hm : ∀ ⦃S T⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (f g : EuclideanSpace ℝ ι → X) (hcharts : (coordinateCube ι 1).EqOn f g)
    (hf : ∀ (S : Finset (EuclideanSpace ℝ ι)) (hS : S.Nonempty),
      (S : Set _) ⊆ coordinateCube ι 2 → δ (S.image f) = meanWidth S hS)
    (hg : ∀ (S : Finset (EuclideanSpace ℝ ι)) (hS : S.Nonempty),
      (S : Set _) ⊆ coordinateCube ι 2 → δ (S.image g) = meanWidth S hS)
    (hboth : δ ((coordinateCubeCorners ι 2).image f ∪ (coordinateCubeCorners ι 2).image g) =
      3 * innerCubeWidth ι)
    (L N : Finset (EuclideanSpace ℝ ι))
    (hL : (L : Set _) ⊆ coordinateCube ι 2) (hN : (N : Set _) ⊆ coordinateCube ι 2) :
    let K := (coordinateCubeCorners ι 1).image f
    δ (K ∪ L.image f ∪ N.image g) = δ (K ∪ L.image f) + δ (K ∪ N.image g) - δ K := by
  let V := coordinateCubeCorners ι 1
  let W := coordinateCubeCorners ι 2
  have hV := coordinateCubeCorners_nonempty ι 1
  have hW := coordinateCubeCorners_nonempty ι 2
  have hsmall : (V : Set _) ⊆ coordinateCube ι 1 := by
    rw [← convexHull_coordinateCubeCorners (zero_le_one' ℝ)]
    exact subset_convexHull _ _
  have hsmall' : (V : Set _) ⊆ coordinateCube ι 2 :=
    hsmall.trans (coordinateCube_one_subset_interior_two.trans interior_subset)
  have hlarge : (W : Set _) ⊆ coordinateCube ι 2 := by
    rw [← convexHull_coordinateCubeCorners (by norm_num : (0 : ℝ) ≤ 2)]
    exact subset_convexHull _ _
  have hside (k : EuclideanSpace ℝ ι → X) (hk : ∀ (S : Finset (EuclideanSpace ℝ ι))
      (hS : S.Nonempty), (S : Set _) ⊆ coordinateCube ι 2 → δ (S.image k) = meanWidth S hS)
      (T : Finset (EuclideanSpace ℝ ι)) (hT : (T : Set _) ⊆ coordinateCube ι 2) :
      δ (V.image k ∪ T.image k ∪ W.image k) = 2 * innerCubeWidth ι := by
    have hVT : (↑(V ∪ T) : Set _) ⊆ coordinateCube ι 2 := by
      simpa only [Finset.coe_union] using Set.union_subset hsmall' hT
    have hVT' : (↑(V ∪ T) : Set _) ⊆ convexHull ℝ (W : Set (EuclideanSpace ℝ ι)) := by
      simpa only [W, convexHull_coordinateCubeCorners (by norm_num : (0 : ℝ) ≤ 2)] using hVT
    have h := hk (W ∪ (V ∪ T)) (hW.mono Finset.subset_union_left)
      (by simpa only [Finset.coe_union] using Set.union_subset hlarge hVT)
    simp only [Finset.image_union] at h
    rw [Finset.union_comm (W.image k)] at h
    apply h.trans
    convert! (meanWidth_union_of_subset_convexHull hW hVT').trans meanWidth_doubled_cube_corners using 1
    congr! 3
  have hK : V.image f = V.image g := Finset.image_congr (fun x hx ↦ hcharts (hsmall hx))
  apply book_independence_of_corner_bounds hs hm (V.image f) (W.image f) (W.image g)
    (L.image f) (N.image g) (hV.image f) (innerCubeWidth ι)
  · exact hf V hV hsmall'
  · exact (hside f hf L hL).le
  · rw [hK]
    exact (hside g hg N hN).le
  · rw [← hboth]
    apply hm ((hW.image f).mono Finset.subset_union_left)
    exact Finset.union_subset_union_left Finset.subset_union_right

end

end

end SpectralBooks
end LinearAlgebra
end OAI

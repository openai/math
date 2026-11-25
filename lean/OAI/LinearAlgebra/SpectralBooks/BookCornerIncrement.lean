import OAI.LinearAlgebra.SpectralBooks.BookCubePrices
import OAI.Geometry.HyperbolicGroups.CATZero

/-! # Diagonal price increments in the doubled cubes

Over any finite set in the second doubled cube containing the inner corners,
a fixed point of the first chart contributes precisely its increment over
the corners alone. Adjoining a point between two occupied sites has zero
increment.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set
open scoped Classical

variable {ι X : Type*} [Fintype ι] {δ : Finset X → ℝ}

/-- The corner independence equation gives a single additive increment for
adjoining the opposite tip to every finite configuration over the corners. -/
theorem opposite_tip_price_of_corner_prices (hs : IntersectingSubmodular δ)
    (hm : ∀ ⦃S T⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (b c : EuclideanSpace ℝ ι → X) (hbc : (coordinateCube ι 1).EqOn b c)
    (hb : ∀ (S : Finset (EuclideanSpace ℝ ι)) (hS : S.Nonempty),
      (S : Set _) ⊆ coordinateCube ι 2 → δ (S.image b) = meanWidth S hS)
    (hc : ∀ (S : Finset (EuclideanSpace ℝ ι)) (hS : S.Nonempty),
      (S : Set _) ⊆ coordinateCube ι 2 → δ (S.image c) = meanWidth S hS)
    (hboth : δ ((coordinateCubeCorners ι 2).image b ∪ (coordinateCubeCorners ι 2).image c) =
      3 * innerCubeWidth ι)
    {z : EuclideanSpace ℝ ι} (hz : z ∈ coordinateCube ι 2)
    {T : Finset (EuclideanSpace ℝ ι)} (hCT : coordinateCubeCorners ι 1 ⊆ T)
    (hT : (T : Set _) ⊆ coordinateCube ι 2) :
    let C := (coordinateCubeCorners ι 1).image b
    δ (insert (b z) (T.image c)) = δ (T.image c) + (δ (insert (b z) C) - δ C) := by
  let C := (coordinateCubeCorners ι 1).image b
  have hcorners : (↑(coordinateCubeCorners ι 1) : Set _) ⊆ coordinateCube ι 1 := by
    rw [← convexHull_coordinateCubeCorners (zero_le_one' ℝ)]
    exact subset_convexHull _ _
  have hsub : C ⊆ T.image c := by
    have heq : C = (coordinateCubeCorners ι 1).image c :=
      Finset.image_congr (fun x hx ↦ hbc (hcorners hx))
    exact heq ▸ Finset.image_subset_image hCT
  have h := doubled_cube_diagonal_independence hs hm b c hbc hb hc hboth {z} T
    (by simpa using hz) hT
  change δ (C ∪ ({z} : Finset _).image b ∪ T.image c) =
    δ (C ∪ ({z} : Finset _).image b) + δ (C ∪ T.image c) - δ C at h
  simp only [Finset.image_singleton, Finset.union_singleton, Finset.insert_union,
    Finset.union_eq_right.mpr hsub] at h
  dsimp only
  linarith

/-- A point between two occupied sites has zero marginal price. The two wire
prices sum to the wire price between the endpoints, so submodularity leaves
no room for a price increase. -/
theorem price_insert_of_dist_add [PseudoMetricSpace X] (hs : IntersectingSubmodular δ)
    (hm : ∀ ⦃S T⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hp : ∀ u v : X, δ {u, v} = dist u v)
    (T : Finset X) {u v z : X} (hu : u ∈ T) (hv : v ∈ T)
    (hz : dist u z + dist z v = dist u v) :
    δ (insert z T) = δ T := by
  by_cases h : z ∈ T
  · simp [h]
  have he : ({u, v} : Finset X) ⊆ T := Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv)
  have hn : ({u, v} : Finset X).Nonempty := Finset.insert_nonempty ..
  have hi : ({z} : Finset X) ⊆ {u, z} ∩ {z, v} := by simp
  have hsub := hs ((Finset.singleton_nonempty z).mono hi)
  have h0 : δ {z} = 0 := by simpa using hp z z
  have hunion : ({u, z} : Finset X) ∪ {z, v} = insert z {u, v} := by
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hunion, hp, hp, hz, ← hp u v] at hsub
  have hin := intersectingSubmodular_iff_diminishingIncrements.mp hs hn he h
  have hnonneg := hm (Finset.singleton_nonempty z) hi
  rw [h0] at hnonneg
  exact le_antisymm (by linarith) (hm ⟨u, hu⟩ (Finset.subset_insert ..))

/-- In a CAT(0) space, contracting an occupied site toward another occupied
site creates a point with zero marginal price. -/
theorem price_insert_catZero_segment [MetricSpace X] (hX : HyperbolicObstruction.CATZero X)
    (hs : IntersectingSubmodular δ) (hm : ∀ ⦃S T⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hp : ∀ u v : X, δ {u, v} = dist u v) (T : Finset X) (u v : X)
    (hu : u ∈ T) (hv : v ∈ T) (t : ℝ) (ht : t ∈ Icc 0 1) :
    δ (insert (HyperbolicObstruction.CATZero.segment hX u v t) T) = δ T := by
  apply price_insert_of_dist_add hs hm hp _ hu hv
  rw [HyperbolicObstruction.CATZero.segment_left hX _ _ ht,
    HyperbolicObstruction.CATZero.segment_right hX _ _ ht]
  ring

end SpectralBooks
end LinearAlgebra
end OAI

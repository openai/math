import OAI.LinearAlgebra.SpectralBooks.DoubledCubes
import OAI.LinearAlgebra.SpectralBooks.BookIndependence

/-! # The mixed diagonal price on finite grids

Diminishing returns lets each page of a union be replaced by a nonempty
subset of equal diagonal price. For the doubled grids these subsets are the
center and outer corners, a fixed number of sites as the mesh is refined.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

section FiniteSets
variable {X : Type*} [DecidableEq X] {δ : Finset X → ℝ}

/-- Replacing two nonempty sets by larger sets of the same prices preserves
the price of their union, for a monotone intersecting-submodular price. -/
theorem union_price_eq_of_eq_on_subsets (hs : IntersectingSubmodular δ)
    (hm : ∀ ⦃S T⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    {A B C D : Finset X} (hA : A.Nonempty) (hC : C.Nonempty)
    (hAB : A ⊆ B) (hCD : C ⊆ D) (eAB : δ A = δ B) (eCD : δ C = δ D) :
    δ (A ∪ C) = δ (B ∪ D) := by
  have h₁ := intersectingSubmodular_union_increment hs hm hA
    (Finset.subset_union_left (s₂ := C)) B
  rw [Finset.union_right_comm, Finset.union_eq_right.mpr hAB, eAB] at h₁
  have h₂ := intersectingSubmodular_union_increment hs hm hC
    (Finset.subset_union_right (s₁ := B)) D
  rw [Finset.union_assoc, Finset.union_eq_right.mpr hCD, eCD] at h₂
  exact le_antisymm (hm (hA.mono Finset.subset_union_left) (Finset.union_subset_union hAB hCD))
    (by linarith)

end FiniteSets

noncomputable section

open scoped Classical

namespace DoubledGridFamily

variable {ι : Type*} [Fintype ι] {X : ℕ → Type*} [∀ n, MetricSpace (X n)]
    {o : ∀ n, X n} (G : DoubledGridFamily ι o)

/-- The complete finite grid of sites on one doubled page. -/
def gridSites (n : ℕ) (k : Bool) : Finset (X n) :=
  Finset.univ.image (G.site n k)

/-- The shared center and the outer corners of one doubled page. -/
def cornerSites (n : ℕ) (k : Bool) : Finset (X n) :=
  insert (o n) (Finset.univ.image (fun z : coordinateCubeCorners ι 1 ↦
    G.site n k ⟨(2 : ℝ) • z.val, double_corner_mem_cubeGrid n z.property⟩))

theorem center_mem_cornerSites (n : ℕ) (k : Bool) : o n ∈ G.cornerSites n k :=
  Finset.mem_insert_self ..

theorem cornerSites_subset_gridSites (n : ℕ) (k : Bool) :
    G.cornerSites n k ⊆ G.gridSites n k := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | h
  · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, G.center n k⟩
  · obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-- When the individual page prices are already achieved on their corners
and center, the mixed corner configuration achieves the full grid union price. -/
theorem grid_union_price_eq_corner_union_price (n : ℕ) (δ : Finset (X n) → ℝ)
    (hs : IntersectingSubmodular δ)
    (hm : ∀ ⦃S T⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hpages : ∀ k, δ (G.cornerSites n k) = δ (G.gridSites n k)) :
    δ (G.gridSites n false ∪ G.gridSites n true) =
      δ (G.cornerSites n false ∪ G.cornerSites n true) :=
  (union_price_eq_of_eq_on_subsets hs hm
    ⟨_, G.center_mem_cornerSites n false⟩ ⟨_, G.center_mem_cornerSites n true⟩
    (G.cornerSites_subset_gridSites n false) (G.cornerSites_subset_gridSites n true)
    (hpages false) (hpages true)).symm

end DoubledGridFamily
end

end SpectralBooks
end LinearAlgebra
end OAI

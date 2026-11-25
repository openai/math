import OAI.LinearAlgebra.SpectralBooks.DoubledCubes
import OAI.LinearAlgebra.SpectralBooks.SiteRestrictionBridge

/-! # The three finite placements of the doubled-grid construction

The indices consist of one shared center, a private copy of every other grid
index on each side, and one auxiliary index for each inner corner. The shared
placement is `none` and the two private placements are `some false` and `some true`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

section

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- The private list in each copy of the grid excludes its center. -/
abbrev NoncentralGrid (ι : Type*) [Fintype ι] (n : ℕ) :=
  {x : cubeGrid ι n // (x : EuclideanSpace ℝ ι) ≠ 0}

/-- The center, the two lists of noncentral grid indices, and the corner auxiliary indices. -/
abbrev DoubledGridSite (ι : Type*) [Fintype ι] (n : ℕ) :=
  BookSite (NoncentralGrid ι n) (NoncentralGrid ι n) ⊕ (coordinateCubeCorners ι 1)

/-- The common center index. -/
abbrev gridCenter : DoubledGridSite ι n := .inl (.inl ())

/-- Use the single center index for the origin in both grids. -/
def gridLabel (k : Bool) (x : cubeGrid ι n) : DoubledGridSite ι n :=
  if hx : (x : EuclideanSpace ℝ ι) = 0 then gridCenter else
    if k then .inl (.inr (.inr ⟨x,hx⟩)) else .inl (.inr (.inl ⟨x,hx⟩))

/-- The three placements in the manuscript's original unit cube. -/
def gridPlacement (page : Option Bool) : DoubledGridSite ι n → EuclideanSpace ℝ ι
  | .inl (.inl _) => 0
  | .inl (.inr (.inl x)) =>
    if page = none ∨ page = some false then (1 / 2 : ℝ) • (x.val : EuclideanSpace ℝ ι) else 0
  | .inl (.inr (.inr x)) =>
    if page = none ∨ page = some true then (1 / 2 : ℝ) • (x.val : EuclideanSpace ℝ ι) else 0
  | .inr z => if page = none then z.val else 0

@[simp] theorem gridPlacement_gridLabel (page : Option Bool) (k : Bool) (x : cubeGrid ι n) :
    gridPlacement page (gridLabel k x) =
      if page = none ∨ page = some k then (1 / 2 : ℝ) • (x : EuclideanSpace ℝ ι) else 0 := by
  cases k <;> by_cases hx : (x : EuclideanSpace ℝ ι) = 0 <;> simp [gridLabel, gridPlacement, gridCenter, hx]

/-- The upper sum of the three wire prices before doubling. -/
def sumPlacedWires (s t : DoubledGridSite ι n) : ℝ :=
  dist (gridPlacement none s) (gridPlacement none t) +
    dist (gridPlacement (some false) s) (gridPlacement (some false) t) +
    dist (gridPlacement (some true) s) (gridPlacement (some true) t)

/-- Exactly two placements retain the original distances of a private grid. -/
theorem sumPlacedWires_gridLabel (k : Bool) (x y : cubeGrid ι n) :
    sumPlacedWires (gridLabel k x) (gridLabel k y) = dist (x : EuclideanSpace ℝ ι) y := by
  cases k <;> simp [sumPlacedWires, dist_smul₀] <;> ring

/-- The finite metric family furnished by a doubled price with the private
equalities and the global upper bound on binary wires. -/
def doubledGridFamilyOfWires {X : ℕ → Type*} [∀ n, MetricSpace (X n)]
    (p : ∀ n, DoubledGridSite ι n → X n)
    (hupper : ∀ n s t, dist (p n s) (p n t) ≤ sumPlacedWires s t)
    (hprivate : ∀ n k (x y : cubeGrid ι n), dist (p n (gridLabel k x)) (p n (gridLabel k y)) =
      sumPlacedWires (gridLabel k x) (gridLabel k y)) :
    DoubledGridFamily ι (fun n ↦ p n gridCenter) where
  site n k x := p n (gridLabel k x)
  center _ _ := by simp [gridLabel]
  wire n k x y := (hprivate n k x y).trans (sumPlacedWires_gridLabel k x y)
  auxiliary n z hz := by
    refine ⟨p n (.inr ⟨z, hz⟩), ?_, fun k ↦ ?_⟩
    · exact (hupper ..).trans (by simp [sumPlacedWires, gridPlacement])
    · apply (hupper ..).trans
      have he : (1 / 2 : ℝ) • (2 : ℝ) • z = z := by rw [smul_smul]; norm_num
      simp only [sumPlacedWires, gridPlacement_gridLabel, he]
      cases k <;> simp [gridPlacement]

end

end

end SpectralBooks
end LinearAlgebra
end OAI

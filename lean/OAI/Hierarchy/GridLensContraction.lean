import OAI.Hierarchy.GridLensWiring
import OAI.Hierarchy.GridLensWireBudget
import OAI.Hierarchy.CorrectionBenchmark

namespace OAI
/-! # Discounted price of a mounted grid contraction -/

namespace Hierarchy.GridLens
open LinearAlgebra.SpectralBooks SiteTensor
open UniversalGrid Catalyst
open scoped BigOperators Classical
noncomputable section

variable {F : Type*} [Field F] {k p L n E : ℕ}
abbrev Space (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- The controller's cell and equality occurrences have coordinates. Every
charged equality and catalyst pair uses its own elementary rail segments.
Literal bits may have different positions at different occurrences. -/
structure Placement (X : Approximation F k p)
    (W : Wiring (Fin E) (Port p X.width) L) (direction : Fin E → Fin k)
    (R : ℝ) (ends : GridDiagonal.Ends (Fin E) → Space k) (n : ℕ) where
  position : W.Sites → Space k
  row : Fin E → Fin k → Fin (n+1)
  cell : Fin L → Fin k → Fin (n+1)
  cell_eq : ∀ i, W.cellAt position i = fun j => cellCenter (cell i) + sites X.width j
  focus : position ∘ GridAddress.outputSite = ends
  paths : PathCertificate direction row R (demandEnds X.width cell (W.edgeAt position))

/-- Exactly the chosen error factors in the expansion, prior to the overall sign. -/
def selected (X : Approximation F k p) (f : (Fin p → Bool) → F) (bad : Finset (Fin L))
    (i : Fin L) : (Port p X.width → Bool) → F :=
  if i ∈ bad then (X.error f).coeff else ideal X.width f

private theorem translate_isometry (c : Space k) : Isometry (fun z : Space k => c+z) := by
  apply Isometry.of_dist_eq
  intro a b
  simp only [dist_eq_norm]
  congr 1
  abel

/-- The estimate is only needed for a surviving term. Zero error factors may
have arbitrary gap and annihilate the complete wiring. -/
theorem Placement.mixed_price {X : Approximation F k p}
    {W : Wiring (Fin E) (Port p X.width) L} [Nonempty W.Sites]
    {direction : Fin E → Fin k} {R : ℝ} {ends : GridDiagonal.Ends (Fin E) → Space k}
    (h : Placement X W direction R ends n) (P : SpectralPlacementPrices F (Space k))
    (f : (Fin p → Bool) → F) {D : ℝ} (gap : X.Gap f D)
    (bad : Finset (Fin L)) (nz : W.mixedEval (selected X f bad) ≠ 0)
    (far : 8*((n:ℝ)+1) ≤ R) :
    P.price (GridDiagonal.raw (W.mixedEval (selected X f bad))) ends ≤
      2*R*E + 18*((k-1:ℕ):ℝ)*E*((n:ℝ)+1)^2/R - (bad.card:ℝ)*D := by
  let base := 2 * ∑ j, (X.width j : ℝ)
  have localCost (i : Fin L) :
      P.price (CorrectionProducts.raw (selected X f bad i)) (W.cellAt h.position i) ≤
        base - (if i ∈ bad then D else 0) := by
    rw [h.cell_eq]
    let shift := fun z : Space k => cellCenter (h.cell i) + z
    have iso : Isometry shift := translate_isometry _
    by_cases hit : i ∈ bad
    · simp only [hit, ite_true, selected]
      rcases X.gap_at gap P shift iso with eq | paid
      · have alive := W.cells_nonzero_of_mixedEval (selected X f bad) nz i
        apply False.elim
        apply alive
        funext bits
        change selected X f bad i bits = 0
        have selected_hit : selected X f bad i =
            (fun b : Port p X.width → Bool => (X.error f).coeff b) := by
          exact ite_eq_left hit
        exact (congrFun selected_hit bits).trans (congrFun eq bits)
      · exact paid
    · simp only [hit, ite_false, selected, sub_zero]
      exact CorrectionBenchmark.price_le (P.pullback shift iso) X.width (ideal X.width f)
  have total := Finset.sum_le_sum (s := Finset.univ) (fun i _ => localCost i)
  have costSum : (∑ i : Fin L, if i ∈ bad then D else 0) = (bad.card:ℝ)*D := by
    simp [Finset.sum_ite_mem, nsmul_eq_mul]
  rw [Finset.sum_sub_distrib,costSum] at total
  have geometry := equality_cost_add_catalysts_le direction h.row R X.width h.cell (W.edgeAt h.position) h.paths
  have allRails := geometry.trans (total_rail_cost_le direction h.row R far)
  have wired := W.mixedEval_price_le P h.position (selected X f bad) nz
  rw [h.focus] at wired
  change (∑ i, dist (W.edgeAt h.position i false) (W.edgeAt h.position i true)) +
    (∑ _ : Fin L, base) ≤ _ at allRails
  linarith

end
end Hierarchy.GridLens

end OAI

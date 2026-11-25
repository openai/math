import OAI.LinearAlgebra.SpectralBooks.GridPriceRealization
import OAI.LinearAlgebra.SpectralBooks.GridSpectralLimit

/-! # Construction of the two doubled spectral cubes

Starting from Euclidean flat prices, extend each finite configuration selected
by doubling to a CAT(0) spectral space. Their pointed ultralimit contains both
charts and retains joint diagonal convexity and all marked corner prices.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Filter HyperbolicObstruction

section

variable {F ι : Type} [Field F] [Fintype ι] [Nonempty ι]

/-- The doubled cube charts with their common inner cube and mixed outer
corner price, in a CAT(0) spectral space over the original field. -/
theorem exists_spectralCubeCharts_of_flat (H : SpectralPlacementPrices F (EuclideanSpace ℝ ι))
    (hflat : ∀ (S : Finset (EuclideanSpace ℝ ι)) (hS : S.Nonempty), H.diagonal S = meanWidth S hS)
    (extendPrice : ∀ (A : FinitePriceSpace F), Nonempty A.carrier →
      ∃ (Y : Type) (_ : MetricSpace Y) (Q : SpectralPlacementPrices F Y),
        CATZero Y ∧ Nonempty (PriceEmbedding A.prices Q))
    (hjoint : ∀ {Y : Type} [MetricSpace Y] (P : SpectralPlacementPrices F Y) (hY : CATZero Y),
      P.JointlyConvexDiagonal hY) :
    ∃ (Y : Type) (_ : MetricSpace Y) (P : SpectralPlacementPrices F Y) (hY : CATZero Y),
      P.JointlyConvexDiagonal hY ∧ Nonempty (SpectralCubeCharts ι P) := by
  obtain ⟨X, m, Q, hX, ⟨G⟩⟩ := exists_catZero_realizedGridDoubling H hflat extendPrice
  let U := Ultrafilter.of (atTop : Filter ℕ)
  let o n := G.place n gridCenter
  let P := SpectralPlacementPrices.metricLimit (o := o) U Q
  refine ⟨MetricLimit.Space (U := U) (o := o), inferInstance, P, MetricLimit.catZero hX, ?_, ?_⟩
  · exact SpectralPlacementPrices.metricLimit_jointlyConvexDiagonal U Q hX (fun n ↦ hjoint (Q n) (hX n))
  · exact ⟨G.spectralCubeCharts hflat U (Ultrafilter.of_le _) hX⟩

end

end SpectralBooks
end LinearAlgebra
end OAI

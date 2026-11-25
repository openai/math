import OAI.LinearAlgebra.SpectralBooks.ConvexOnPrice
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI
/-! # The Euclidean spectral flats used in the arithmetic separation -/

namespace Hierarchy

open LinearAlgebra.SpectralBooks

/-- The restriction of the price system to the full Euclidean flat. The wire
axiom of the system recovers the Euclidean distance at every pair of sites. -/
abbrev HasSpectralFlat (F : Type*) [Field F] (d : ℕ) : Prop :=
  Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin d)))

/-- Homogeneous flat prices as in the paper. All tensor formats use the same choice of prices. -/
structure HomogeneousFlat (F : Type*) [Field F] (d : ℕ) where
  prices : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin d))
  translate {I : Type} [Fintype I] (T : SiteTensor.Raw.{0} I F)
    (x : I → EuclideanSpace ℝ (Fin d)) (v : EuclideanSpace ℝ (Fin d)) :
    prices.price T (fun i => x i + v) = prices.price T x
  convex {I : Type} [Fintype I] (T : SiteTensor.Raw.{0} I F) :
    ConvexOn ℝ Set.univ (prices.price T)
  dilate {I : Type} [Fintype I] (T : SiteTensor.Raw.{0} I F)
    (x : I → EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : 0 < r) :
    prices.price T (r • x) = r * prices.price T x

/-- The geometric input of the graph-contraction classification in the field of coefficients. -/
def AllHomogeneousFlats (F : Type*) [Field F] : Prop :=
  ∀ d : ℕ, 0 < d → Nonempty (HomogeneousFlat F d)

end Hierarchy

end OAI

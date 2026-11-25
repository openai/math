import OAI.LinearAlgebra.SpectralBooks.ShiftedCrossing.ShortenLimits
import OAI.LinearAlgebra.SpectralBooks.ShiftedCrossing.ShortenFinite

/-! # The limiting shifted crossing in a normed spectral space -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace ShiftedCrossing

open Real Filter
open scoped Topology

/-- Apply the two-cut tensor bound at each admissible size and take normalized
logarithmic rates. The sum overhead depends only on the placement. -/
theorem AsymptoticFactorizations.shiftedCrossingCost {K E : Type*} [Field K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (h : AsymptoticFactorizations K) (P : SpectralPlacementPrices K E) :
    ShiftedCrossingCost E := by
  intro x y hx hy t u δ ht hu hlo hhi p m
  obtain ⟨dx, dy, rp, rm, bp, bm, hfac, hdx, hdy, hr, hbp, hbm⟩ :=
    h t u δ ht hu hlo hhi
  obtain ⟨C, finite⟩ := exists_finite_placement_bound P x y p m hx hy
  apply cost_limit (C := C) (Rp := fun n => Real.logb 2 (rp n))
    (Rm := fun n => Real.logb 2 (rm n)) (norm_nonneg p) (norm_nonneg m) hdx hdy hbp hbm hr
  filter_upwards [hfac] with n hn
  obtain ⟨hx, hy, ⟨F⟩⟩ := hn
  exact finite hx hy F

end ShiftedCrossing

end SpectralBooks
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.SpectralBooks.BookDilation
import OAI.LinearAlgebra.SpectralBooks.PriceBlowup

/-! # Spectral prices on the whole three-page book

An isometric copy of the central bounded slabs in a spectral space over a
field induces a spectral price on the entire book over that same field.
All finite placed tensors use the same ultrafilter of integer magnifications.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open Filter Topology

variable {E X K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [PseudoMetricSpace X] [Field K]

/-- The prices are divided by this length scale at the integer magnifications. -/
private def bookScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

private theorem bookApprox_tendsto (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : boundedBook E → X) (hf : Isometry f) (p q : Book E) :
    Tendsto (fun n => dist (f (bookApprox n p)) (f (bookApprox n q)) / bookScale n)
      (U : Filter ℕ) (𝓝 (dist p q)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(eventually_bookApprox_dist p q).filter_mono hU] with n hn
  simpa only [bookScale, hf.dist_eq, div_inv_eq_mul, mul_comm] using hn.symm

/-- Rescale the prices from the bounded slabs by the same integer factors
as their distances. This computes all limiting prices over the original field. -/
def SpectralPlacementPrices.bookOfIsometry (P : SpectralPlacementPrices K X)
    (f : boundedBook E → X) (hf : Isometry f) : SpectralPlacementPrices K (Book E) :=
  P.blowup (Ultrafilter.of atTop) bookScale (fun n => by dsimp [bookScale]; positivity)
    (fun n p => f (bookApprox n p)) boundedBookOrigin.val
    (bookApprox_tendsto _ (Ultrafilter.of_le _) f hf)

end

end

end SpectralBooks
end LinearAlgebra
end OAI

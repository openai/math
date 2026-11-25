import OAI.Computability.NearSquareRoot.KernelBinaryQuerySigns
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleDiagonal

/-! # The diagonal geometry block is the physical binary query -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BinaryQuery
open OAI.LinearAlgebra.FiniteFourier KernelPass KernelNormalization Matrix
noncomputable section

abbrev physical (m u : ℕ) := splitLinear m u

/-- Pulling back the diagonal geometric transfer with the same numbering of
the entire physical column gives the ordinary quadratic query. -/
theorem transfer_self {m L b : ℕ} (G : BitRoutingGeometry 2 L b) (j : Fin m) (v : BitLabel L b) :
    (G.transfer binaryRoot 1 1 j v v).submatrix (physical m (G.D-1)) (physical m (G.D-1)) =
      query (u:=G.D-1) j := by
  rw [G.transfer_self]
  simp only [Units.val_one, ZMod.val_one, pow_one]
  ext y x
  rw [query, localize_apply]
  simp only [Matrix.submatrix_apply, LinearMap.toMatrix'_apply]
  congr! 10

end
end BinaryQuery

end NearSquareRoot
end Computability
end OAI

import OAI.Computability.NearSquareRoot.SynchronizedDilationPairs
import OAI.Computability.NearSquareRoot.SynchronizedPrimitive
import OAI.Computability.NearSquareRoot.SynchronizedShortTransform

/-! # Primitive matching for the calibrated dilation

Each frequency in the padded transform pairs with the same frequency in the
borrowed half. The bound on the calibrated multiplier supplies both phase
factorizations required by the forward and adjoint short-layer schedules.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix SynchronizedPair

private theorem dilation_in_sum_order {ι : Type} [DecidableEq ι] (z : ι → ℂ) :
    dilation z = (blockDiagonal fun i => pair (z i)).submatrix dilationAddress dilationAddress := by
  ext i j
  have h := congrFun (congrFun (dilation_blocks z) (dilationAddress i)) (dilationAddress j)
  simpa only [submatrix_apply, Equiv.symm_apply_apply] using h

theorem dilation_shortLayer {ι : Type} [DecidableEq ι] (z : ι → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1 / 2) : ShortLayer (dilation z) := by
  rw [dilation_in_sum_order]
  exact ShortLayer.pairs dilationAddress.symm _ (fun i => pair_threeWalsh (hz i))
    (fun i => adjoint_pair_threeWalsh (hz i))

theorem dilation_adjoint_shortLayer {ι : Type} [DecidableEq ι] (z : ι → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1 / 2) : ShortLayer (dilation z)ᴴ := by
  rw [dilation_in_sum_order, Matrix.conjTranspose_submatrix, Matrix.blockDiagonal_conjTranspose]
  exact ShortLayer.pairs dilationAddress.symm _ (fun i => adjoint_pair_threeWalsh (hz i))
    (fun i => by simpa only [Matrix.conjTranspose_conjTranspose] using pair_threeWalsh (hz i))

/-- The calibrated matching and its adjoint both use three Walsh rounds for
all padded frequencies, with identical choices of paired addresses. -/
theorem calibrated_dilation_shortLayer {a r : ℕ} (ha : 0 < a) :
    ShortLayer (dilation (calibratedMultiplier a r)) ∧
    ShortLayer (dilation (calibratedMultiplier a r))ᴴ :=
  ⟨dilation_shortLayer _ (fun i => (calibratedMultiplier_lt_half ha i).le),
   dilation_adjoint_shortLayer _ (fun i => (calibratedMultiplier_lt_half ha i).le)⟩

end ShortFourier

end NearSquareRoot
end Computability
end OAI

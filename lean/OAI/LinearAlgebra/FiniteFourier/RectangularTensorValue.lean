import OAI.LinearAlgebra.FiniteFourier.PhaseTensorValue
import OAI.LinearAlgebra.FiniteFourier.RectanglePoint

/-! # The rectangle value used in the coefficient estimate

One spectral point evaluates the lifted matrices of every slot count. On one
slot the identification with the original matrix is an independent reindexing
of the row and column labels.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

/-- At a nondegenerate rectangle with its semiperimeter normalization, the
matrix lift is one `TensorValue` simultaneously in all finite tensor powers. -/
theorem exists_rectangular_tensorValue {K : Type*} [Field K] (P : SpectralPlacementPrices K Plane)
    (O I : Type) [Fintype O] [Fintype I] {s c : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hnormal : P.price (Raw.diagonal (Fin 4) K (Fin 2)) (rectangleSites (2*s) (2*c)) = 2*(c+s)) :
    ∃ ν : TensorValue K (O × I),
      (∀ k a, ν.price k a = rectangleValue (fourierPhasePrice P) (slotMatrix a) s c) ∧
      ∀ M : Matrix O I K, ν.price 1 (slotPower (Function.uncurry M) 1) =
        rectangleValue (fourierPhasePrice P) M s c := by
  obtain ⟨φ, hφ⟩ := exists_rectangle_point P hs hc hnormal
  refine ⟨tensorValueOfPhasePoint φ O I, fun _ a ↦ hφ _ _ (slotMatrix a), ?_⟩
  intro M
  exact (phasePointValue_slotPower_one φ (Function.uncurry M)).trans (hφ O I M)

end

end

end FiniteFourier
end LinearAlgebra
end OAI

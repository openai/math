import OAI.LinearAlgebra.SpectralBooks.BookRank
import OAI.LinearAlgebra.SpectralBooks.WireEvaluation

/-! # Recovering placed wires from binary distances

The metric is specified by the price of a binary wire. The dimension law
extends each of these identities to all positive wire dimensions.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
section

/-- It suffices to identify the three binary wire prices with the three
distances in a placement. -/
def PlacedWires.ofBinary {F : Type*} [Field F] {X : Type*} [PseudoMetricSpace X]
    {p : Fin 3 → X} {d : ℝ} (φ : RankFunctional F) (hd : 0 ≤ d)
    (h12 : d * Real.logb 2 (φ.value (wire12 F 2)) = dist (p 0) (p 1))
    (h23 : d * Real.logb 2 (φ.value (wire23 F 2)) = dist (p 1) (p 2))
    (h31 : d * Real.logb 2 (φ.value (wire31 F 2)) = dist (p 2) (p 0)) :
    PlacedWires F p d where
  point := φ
  nonneg := hd
  price12 n hn := by
    have h := φ.logb_wireValue 0 hn
    change Real.logb 2 (φ.value (wire12 F n)) = Real.logb 2 (φ.value (wire12 F 2)) * _ at h
    rw [h, ← mul_assoc, h12]
  price23 n hn := by
    have h := φ.logb_wireValue 1 hn
    change Real.logb 2 (φ.value (wire23 F n)) = Real.logb 2 (φ.value (wire23 F 2)) * _ at h
    rw [h, ← mul_assoc, h23]
  price31 n hn := by
    have h := φ.logb_wireValue 2 hn
    change Real.logb 2 (φ.value (wire31 F n)) = Real.logb 2 (φ.value (wire31 F 2)) * _ at h
    rw [h, ← mul_assoc, h31]

end

end

end SpectralBooks
end LinearAlgebra
end OAI

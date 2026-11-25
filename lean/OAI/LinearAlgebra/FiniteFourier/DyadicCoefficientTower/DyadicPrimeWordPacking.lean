import OAI.LinearAlgebra.FiniteFourier.DyadicCoefficientTower.DyadicCoefficientsAxis
import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicPrimeAxisWords
import OAI.LinearAlgebra.FiniteFourier.DyadicCoefficientTower.DyadicFourierAxis

/-! # Uniform cost of the prime-axis transforms on a protected dyadic list -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace DyadicCoefficientTower

open Matrix Deformation

variable {η : ℝ} {n B : ℕ} {D : DyadicAxisPacking GaussianRationals η n B} {L : Finset ℕ}
  (T : DyadicCoefficientTower D L) {p : ℕ} [Fact p.Prime] [Nontrivial T.Order]
  {J : Type} [Fintype J] [DecidableEq J]

/-- The two actual basis changes of a packed prime axis, over the common coefficient
order. The workspace consists of thirteen registers per nonzero cyclic address. -/
theorem primeAxis_words (hp : p ∈ D.packing.axes)
    (rows : J ≃ Option (Fin (p-1))) (cols : J ≃ ZMod p) :
    OccupiedWord (Fin (13*(p-1))) (6400*(1+Nat.clog 2 (2+B))+8)
      ((T.primeAxis hp).forward.submatrix rows cols) ∧
    OccupiedWord (Fin (13*(p-1))) (6400*(1+Nat.clog 2 (2+B))+8)
      ((T.primeAxis hp).backward.submatrix cols rows) := by
  have hpos := T.axis_large hp
  have hle := (D.axis_properties T.width hp).2.2.1
  have hsep := T.axisRoot_separate hp
  apply (T.primeAxis hp).occupiedWord_pair rows cols (T.axis_unit hp (RingHom.id _))
    (T.axisRoot_pow hp) hsep
  · apply T.fourierWord (RingHom.id _) (by omega) (by omega) T.split (T.axisRoot hp).isUnit hsep
    exact Or.inl (geometricMatrix_eq_dftMatrix _ _)
  · apply T.fourierWord (RingHom.id _) (by omega) (by omega) T.split (T.axisRoot hp).isUnit hsep
    exact Or.inr (congrArg Inv.inv (geometricMatrix_eq_dftMatrix _ _))

end DyadicCoefficientTower

end FiniteFourier
end LinearAlgebra
end OAI

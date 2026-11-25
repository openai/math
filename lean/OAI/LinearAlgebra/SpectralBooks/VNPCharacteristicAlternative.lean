import OAI.LinearAlgebra.SpectralBooks.StudentTestFromFlat
import OAI.LinearAlgebra.SpectralBooks.VNP.BorderStretchReduction

/-! # The characteristic alternative via the effective boundary and weighted simulation

This reduction exposes the two remaining VNP constructions behind the circuit branch. The
conclusion quantifies over every field of the chosen characteristic.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open VNP

universe u

theorem characteristicAlternative_of_boundary_protocols
    (k : Type) [Field k] (p : ℕ) [CharP k p]
    (protocols : ∀ D : ℕ, 2 ≤ D → Crossing.HasProfileShortening k D →
      ∃ ε : ℝ, 0 < ε ∧ ∃ allowed : ∀ n, Set (PinLayout n (stretchBudget ε n)),
        WeightedProgramSimulation ε allowed ∧ EffectivePrimeDescent k ε allowed) :
    CharacteristicAlternative.{u} p := by
  apply characteristicAlternative_of_borderStretch k p
  intro D hD hs
  exact borderStretch_of_simulation_and_descent k D hD hs (protocols D)

end SpectralBooks
end LinearAlgebra
end OAI

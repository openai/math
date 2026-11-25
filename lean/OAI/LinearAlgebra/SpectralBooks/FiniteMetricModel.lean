import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Finite metric configurations for spectral norm rigidity -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- Every finite labeled configuration of `E` occurs isometrically in `X`. -/
def FiniteMetricModel (X E : Type*) [PseudoMetricSpace X] [PseudoMetricSpace E] : Prop :=
  ∀ {I : Type} [Fintype I] (p : I → E), ∃ q : I → X, ∀ i j, dist (q i) (q j) = dist (p i) (p j)

/-- The finite-configuration form of the manuscript's norm rigidity criterion.
Translations into the sector let us use scale one here. -/
def SectorNormRigidity (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
    FiniteMetricModel X E → Nonempty (InnerProductSpace ℝ E)

/-- A separate positive scale is allowed for each finite configuration. -/
def ScaledFiniteMetricModel (X E : Type*) [PseudoMetricSpace X] [PseudoMetricSpace E] : Prop :=
  ∀ {I : Type} [Fintype I] (p : I → E), ∃ c : ℝ, 0 < c ∧ ∃ q : I → X,
    ∀ i j, dist (q i) (q j) = c * dist (p i) (p j)

/-- Norm rigidity for finite configurations realized at independent positive scales. -/
def ScaledSectorNormRigidity (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
    ScaledFiniteMetricModel X E → Nonempty (InnerProductSpace ℝ E)

end SpectralBooks
end LinearAlgebra
end OAI

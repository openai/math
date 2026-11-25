import OAI.LinearAlgebra.FiniteFourier.Circuit
import OAI.LinearAlgebra.FiniteFourier.LayerSynchronization
import OAI.Computability.FourierCircuit.Triangular
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # The two companion circuit estimates used by the grid theorem

Specialization of the integral polynomial-multiplication construction at one
fixed operand gives the truncated convolution estimate. The second estimate
is the companion construction on tensor powers of the integral unit shear.
The same constants apply across all fields.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- The fixed-operand convolution bound used in the grid proof. -/
def FixedConvolutionBound (K : Type*) [Field K] (β C : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ f : PowerSeries K,
    (complexity (ExactFourier.CoefficientTime.truncMatrix n f) : ℝ) ≤
      C * (n : ℝ) * (1 + Real.logb 2 n)^β

/-- The integral `2×2` shear tensor circuit estimate at a fixed exponent. -/
def ShearTensorBound (K : Type*) [CommSemiring K] (β C : ℝ) : Prop :=
  ∀ j : ℕ, (complexity (gridTensor (fun _ : Fin j => unitShear K)) : ℝ) ≤
    C * (2 : ℝ)^j * (1 + (j : ℝ))^β

/-- The two companion inputs, with constants uniform over the ground fields. -/
def UniformGridInputs : Prop :=
  ∀ β : ℝ, 1 / 2 < β → β < 1 → ∃ C > (0 : ℝ), ∀ (K : Type*) [Field K],
    FixedConvolutionBound K β C ∧ ShearTensorBound K β C

end FiniteFourier
end LinearAlgebra
end OAI

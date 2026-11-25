import OAI.LinearAlgebra.FiniteFourier.IntegralConvolutionTheorem
import OAI.LinearAlgebra.FiniteFourier.IntegralTensorBound
import OAI.LinearAlgebra.FiniteFourier.GridUpper
import OAI.LinearAlgebra.FiniteFourier.CyclicBounds

/-! # Unconditional upper bounds for finite abelian Fourier transforms

The integer convolution and shear circuits can be specialized in any
characteristic. Their constants precede the choices of group, field and roots.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

universe u v

/-- The two integral constructions that supply the geometric-grid algorithm. -/
theorem integralCircuitInputs : IntegralCircuitInputs :=
  IntegralCircuitInputs.of_separate_bounds (fun _ h _ => integralConvolutionBound h)
    (fun _ h _ => integralShearBound h)

/-- The upper estimate of Theorem 1.1, uniformly in the group and field.
`uniformFourierUpper.both` gives both directions with the same constant and
`uniformFourierUpper.cyclic` gives the positive- and negative-phase DFTs. -/
theorem uniformFourierUpper : UniformFourierUpper.{u,v} :=
  uniformFourierUpper_of_integral_bounds integralCircuitInputs

/-- The upper bound of Theorem 1.1 for both transform directions. -/
theorem fourierComplexity_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ (G : Type u) (K : Type v) [AddCommGroup G] [Fintype G] [Field K],
      Admissible G K → 2 ≤ Fintype.card G →
      let N : ℝ := Fintype.card G
      let U := C * N * (1 + Real.logb 2 N) ^ ((1 : ℝ)/2 + ε)
      (complexity (fourierMatrix G K) : ℝ) ≤ U ∧
        (complexity (inverseFourierMatrix G K) : ℝ) ≤ U := uniformFourierUpper.both hε

end FiniteFourier
end LinearAlgebra
end OAI

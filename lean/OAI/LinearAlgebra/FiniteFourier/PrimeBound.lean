import OAI.LinearAlgebra.FiniteFourier.PrimeConcreteBatch
import OAI.LinearAlgebra.FiniteFourier.PrimeKernelUniform
import OAI.LinearAlgebra.FiniteFourier.PrimeRectanglePencil

/-! # Fourier circuits on tensor powers of a fixed prime radix -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

universe u

/-- The rectangle system implements each ordinary prediction stage and Hermite
repair turns the routed stages into a full batch of independent transforms. -/
theorem primeRepairedBatches (ℓ : ℕ) [Fact ℓ.Prime] : PrimeRepairedBatches.{u} ℓ := by
  intro K _ _ _ L v m S ζ hζ _ p ρ hρ hm hcong
  exact primeKernelBatch_of_compiledStage S hζ p ρ hρ hm hcong (S.realizesPencil hζ p)

/-- Prime Fourier tensor powers have linear volume times `(1+k)^θ` circuit
size for every `θ > 1/2`, uniformly over all specializations of their integral
cyclotomic coefficients and all numbers of digits. -/
theorem uniformPrimeKernelBound (ℓ : ℕ) [Fact ℓ.Prime] {θ : ℝ} (hθ : 1/2 < θ) :
    UniformPrimeKernelBound.{u} ℓ θ :=
  uniformPrimeKernelBound_of_repairedBatches hθ (primeRepairedBatches ℓ)

end FiniteFourier
end LinearAlgebra
end OAI

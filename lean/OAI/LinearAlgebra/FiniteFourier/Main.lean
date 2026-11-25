import OAI.LinearAlgebra.FiniteFourier.BatchedTheorem
import OAI.LinearAlgebra.FiniteFourier.CompanionUpper
import OAI.LinearAlgebra.FiniteFourier.FourierTheorem
import OAI.LinearAlgebra.FiniteFourier.CompanionStretch
import OAI.Computability.FourierCircuit.Main

/-! # Circuit complexity of finite abelian Fourier transforms -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

universe u v

/-- Uniform forward and inverse gate bounds over every admissible group and field,
including the lower bound for geometric feedback border complexity. -/
theorem fourierComplexity : FourierComplexityTheorem.{u,v} :=
  fourierComplexityTheorem_of_estimates uniformFourierBorderLower uniformFourierUpper

end FiniteFourier
end LinearAlgebra
end OAI

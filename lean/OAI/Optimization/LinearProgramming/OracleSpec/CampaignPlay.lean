import OAI.Optimization.LinearProgramming.OracleSpec.PriceRealization
import OAI.Optimization.LinearProgramming.PriceGame.ControlExchanges

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec

variable {N : ℕ} {α : Type*}
open PriceGame

/-- The independently specified interleaving of public replies and the source
algorithm emit the same words, in the same order, against every adaptive oracle. -/
theorem serializedPlay_eq_wirePlay (reply : Transcript → Word → Bool)
    (p : Computation N α) (hist : Transcript) :
    serializedPlay reply p hist = Control.wirePlay reply p hist := by
  induction p generalizing hist with
  | pure => rfl
  | ask q next ih => exact ih _ _

end OracleSpec
end LinearProgramming
end Optimization
end OAI

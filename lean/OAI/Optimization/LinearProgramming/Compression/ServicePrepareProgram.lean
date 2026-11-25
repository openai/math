import OAI.Optimization.LinearProgramming.Compression.ServiceParameters
import OAI.Optimization.LinearProgramming.Compression.ServiceSave
import OAI.Optimization.LinearProgramming.Compression.ServiceClean
import OAI.Optimization.LinearProgramming.Compression.ProxyEvenInput

/-! The fixed finite-window setup for a numerical minor request over an ordered field. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ServicePrepare
open RAM ServiceBudget

/-- Executable compiler with three natural constants shared by every input. -/
def withParameters (coefficient exponent constant : ℕ) : Block :=
  .seq (monomialCapacity 27 coefficient exponent constant)
    (.seq ServiceSave.saveLive (.seq ServiceClean.clearForNumeric ServiceFill.evenInput))

/-- A polynomial time certificate fixes these global compiler parameters once. -/
noncomputable def block (time : Polynomial ℕ) (rom : ℕ) : Block :=
  withParameters (coefficient time) (exponent time) (rom+114)

end ServicePrepare
end Compression
end LinearProgramming
end Optimization
end OAI

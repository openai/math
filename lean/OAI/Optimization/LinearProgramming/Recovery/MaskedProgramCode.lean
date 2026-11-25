import OAI.Optimization.LinearProgramming.Recovery.MaskedInput
import OAI.Optimization.LinearProgramming.Recovery.MaskedTable

/-! The fixed support-mask input program and its dimension-only instruction budget,
shared by rational and ordered-field decision and witness callers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace MaskedInput

open RAM Geometry

def program : Block := .seq snapshot MaskedTable.program

noncomputable def programTime (h n : ℕ) := time h n+uniformTableTime n n (4*n+11)

end MaskedInput
end Recovery
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.Lattice.BitBasicCodes
import OAI.Computability.QuantumFactoring.BitStackRationals

/-! Data carried by a residual query. The physical frames do not require the geometry proofs. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver
open ExactQuantumFactoring.BitStackProgram

abbrev Row := List ℤ
def rowPairCode := prodCode intRowCode intRowCode

namespace Probe
abbrev Params := (ℕ × ℕ) × IntMatrix
abbrev MaxState := (Params × IntMatrix) × (Row × Row)
abbrev Pivot := Params × Row
abbrev Ratio := (Pivot × (Row × IntMatrix)) × ((ℤ × ℕ) × (ℕ × List ℚ))
abbrev Carry := (MaxState ⊕ MaxState) ⊕ (Pivot ⊕ Ratio)
abbrev Result := Bool × List ℚ
abbrev Action := Result ⊕ (Row × Carry)

end Probe
end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI

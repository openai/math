import OAI.Computability.QuantumFactoring.BitStackIntegers
import OAI.Computability.QuantumFactoring.BitStackListCode

/-! The two row-major signed matrix codecs used by the whole bit-machine chain.
They are independent of a native LLL state or an ambient real geometry. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram

abbrev IntMatrix := List (List ℤ)
def intRowCode := listCode intCode
def intMatrixCode := listCode intRowCode

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI

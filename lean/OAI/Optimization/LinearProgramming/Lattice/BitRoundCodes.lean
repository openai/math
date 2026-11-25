import OAI.Optimization.LinearProgramming.Lattice.BitRoundState
import OAI.Optimization.LinearProgramming.Lattice.BitProbeCodes

/-! Physical framing of persistent rounding calls. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure OracleSpec

def envCode : Env → Word := prodCode (prodCode inputCode unaryCode) intMatrixCode
def carryCode : Carry → Word := prodCode envCode Probe.carryCode
def actionCode : Action → Word := sumCode id (prodCode id carryCode)

end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI

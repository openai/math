import OAI.Optimization.LinearProgramming.Lattice.BitProbeTypes
import OAI.Computability.QuantumFactoring.BitStackSums
import OAI.Computability.QuantumFactoring.BitStackNaturals

/-! Raw encodings of the finite probe continuations and outgoing actions. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver
namespace Probe

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure

def paramsCode : Params → List Bool := prodCode (prodCode unaryCode unaryCode) intMatrixCode
def maxBaseCode := prodCode paramsCode intMatrixCode
def maxCode : MaxState → List Bool := prodCode maxBaseCode rowPairCode
def pivotCode : Pivot → List Bool := prodCode paramsCode intRowCode
def ratListCode := listCode ratCode
def counterCode := prodCode intCode Nat.bits
def remainingCode := prodCode unaryCode ratListCode
def ratioLeftCode := prodCode pivotCode (prodCode intRowCode intMatrixCode)
def ratioRightCode := prodCode counterCode remainingCode
def ratioCode : Ratio → List Bool := prodCode ratioLeftCode ratioRightCode
def carryLeftCode := sumCode maxCode maxCode
def carryRightCode := sumCode pivotCode ratioCode
def carryCode : Carry → List Bool := sumCode carryLeftCode carryRightCode
def resultCode : Result → List Bool := prodCode boolCode ratListCode
def actionCode : Action → List Bool := sumCode resultCode (prodCode intRowCode carryCode)

end Probe
end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI

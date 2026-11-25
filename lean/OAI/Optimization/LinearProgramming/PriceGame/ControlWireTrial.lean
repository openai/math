import OAI.Optimization.LinearProgramming.PriceGame.ControlWire
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialPackets

/-! First-order encodings for every stack frame and program counter of the trial evaluator.
The control tag uses exactly two bits; every payload is ordinary binary data. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure (boolCode)
open Trial

def nodeInputCode (i : NodeInput) : List Bool :=
  prodCode Nat.bits (prodCode (listCode (listCode ratCode)) (listCode ratCode))
    (i.level,i.history,i.weights)

def preparedCode (p : Prepared) : List Bool :=
  prodCode boolCode (prodCode (listCode ratCode)
    (prodCode (listCode (listCode ratCode)) (listCode ratCode)))
      (p.isProbe,p.baseline,p.allocation,p.deepWeights)

def completedCode (c : Completed) : List Bool :=
  prodCode (listCode ratCode) (prodCode (listCode ratCode)
    (prodCode (listCode ratCode) packedRoundCode)) (c.baseline,c.mapped,c.gains,c.child)

end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

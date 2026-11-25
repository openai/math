import OAI.Optimization.LinearProgramming.PriceGame.ControlWireTrial
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialCore

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open ExactQuantumFactoring.BitStackProgram
open Trial

def frameCode (f : Frame NodeInput Prepared Completed) : List Bool :=
  prodCode Nat.bits (prodCode Nat.bits (prodCode nodeInputCode
    (prodCode (listCode completedCode) preparedCode)))
    (f.childFuel,f.remaining,f.input,f.prefix,f.prepared)

def pcCode : PC NodeInput Prepared PackedRound Completed → List Bool
  | .enter fuel i => false :: false :: prodCode Nat.bits nodeInputCode (fuel,i)
  | .schedule fuel rem i xs => false :: true :: prodCode Nat.bits (prodCode Nat.bits
      (prodCode nodeInputCode (listCode completedCode))) (fuel,rem,i,xs)
  | .returned out => true :: false :: packedRoundCode out
  | .feedback f out replies => true :: true :: prodCode frameCode (prodCode packedRoundCode id)
      (f,out,replies)

def stateCode (s : State NodeInput Prepared PackedRound Completed) : List Bool :=
  prodCode pcCode (listCode frameCode) (s.pc,s.stack)

end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

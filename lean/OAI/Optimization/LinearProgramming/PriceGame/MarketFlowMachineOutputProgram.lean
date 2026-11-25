import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineOutput
import OAI.Optimization.LinearProgramming.PriceGame.MarketBitStackCanonicalCore

/-! One polynomial finite bit program computes canonical prices and the dense allocation. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace FlowMachine
namespace Output

open ExactQuantumFactoring.BitStackProgram

def output : Argument → Answer := finish GridMachine.Readout.canonical

noncomputable def outputP : Procedure argumentCode answerCode output :=
  finishP GridMachine.Readout.canonicalP

theorem output_deploy (o : OracleSpec.WordOracle) (x : Argument) :
    (OracleSpec.BitCode.deploy outputP).ComputesWithin o (argumentCode x)
      (3*outputP.bound.eval (argumentCode x).length+2*(argumentCode x).length+2)
      (fun hist bits => hist=[] ∧ bits=answerCode (output x)) :=
  OracleSpec.BitCode.deploy_correct outputP o x

end Output
end FlowMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI

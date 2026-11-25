import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineOutput
import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineAllocationSpec
import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentMachineEncoding

/-! Reading the real final packed transshipment state produces the public
market output in expert-major ordering. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace FlowMachine
namespace Output

open Augment Augment.Machine
open ExactQuantumFactoring.BitStackProgram

variable {m g : ℕ} (I : Input m g) (qty : Fin m → ℕ) (D : ℕ) (s : State m g)

theorem finalFrame_pack (y : Fin g → ℚ) :
    finalFrame (List.ofFn y,(List.ofFn qty,packEnv I D s)) =
      inputFrame I.positive qty I.available I.intercept s.flow D y := rfl

theorem finish_pack (hd : 0 < D)
    (hc : ∀ e j, I.available e j = true → NumberBounds.OnGrid D (I.intercept e j))
    (prices : Environment → Prices)
    (hp : prices (packEnv I D s) = List.ofFn (pricesFromFlow I.positive I.available I.intercept s.flow)) :
    let out := outputFromFlow I.positive qty I.available I.intercept s.flow
    finish prices (List.ofFn qty,packEnv I D s) = (List.ofFn out.1,packedCells out.2) := by
  dsimp only [finish, assemble]
  rw [hp, finalFrame_pack, allocations_inputFrame I.positive qty I.available I.intercept s.flow D _ hd hc]
  rfl

/-- Executing the composed bit program on the packed state yields the complete public price
and allocation vector, with polynomial cost measured in the actual input word length. -/
theorem finish_deploy_pack (hd : 0 < D)
    (hc : ∀ e j, I.available e j = true → NumberBounds.OnGrid D (I.intercept e j))
    {prices : Environment → Prices} (canon : Procedure envCode pricesCode prices)
    (hp : prices (packEnv I D s) = List.ofFn (pricesFromFlow I.positive I.available I.intercept s.flow))
    (o : OracleSpec.WordOracle) :
    let input := argumentCode (List.ofFn qty,packEnv I D s)
    let out := outputFromFlow I.positive qty I.available I.intercept s.flow
    (OracleSpec.BitCode.deploy (finishP canon)).ComputesWithin o input
      (3*(finishP canon).bound.eval input.length + 2*input.length+2)
      (fun history bits => history=[] ∧ bits=answerCode (List.ofFn out.1,packedCells out.2)) := by
  have h := OracleSpec.BitCode.deploy_correct (finishP canon) o (List.ofFn qty,packEnv I D s)
  rwa [finish_pack I qty D s hd hc prices hp] at h

end Output
end FlowMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineAllocation
import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentMachineStep
import OAI.Optimization.LinearProgramming.PriceGame.ControlScoreQuantize

/-! The terminal packet combines the canonical price computation with allocation
extraction. The canonical price vector is evaluated once and retained for both outputs. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace FlowMachine
namespace Output

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Augment.Machine

abbrev Argument := List ℕ × Environment
abbrev argumentCode := prodCode flowCode envCode
abbrev Answer := Prices × List ℚ
abbrev answerCode := prodCode pricesCode pricesCode
abbrev Priced := Prices × Argument
abbrev pricedCode := prodCode pricesCode argumentCode

def finalFrame (x : Priced) : Frame :=
  ((x.2.1,x.2.2.1.1.toNat),(x.2.2.1.2,(x.2.2.2.1,x.1)))

noncomputable def finalFrameP : Procedure pricedCode frameCode finalFrame := by
  let prices := first pricesCode argumentCode
  let input := second pricesCode argumentCode
  let qty := (first flowCode envCode).comp input
  let env := (second flowCode envCode).comp input
  let fixed := (first fixedCode dynCode).comp env
  let dyn := (second fixedCode dynCode).comp env
  let den := Control.Native.intToNatP.comp ((first intCode Rows.statCode).comp fixed)
  let stat := (second intCode Rows.statCode).comp fixed
  let flow := (first flowCode banksCode).comp dyn
  exact ((qty.pair den).pair (stat.pair (flow.pair prices))).congrFun (fun _ => rfl)

def assemble (x : Priced) : Answer :=
  (x.1,allocations (finalFrame x))

noncomputable def assembleP : Procedure pricedCode answerCode assemble :=
  (first pricesCode argumentCode).pair (allocationsP.comp finalFrameP)

def finish (prices : Environment → Prices) (x : Argument) : Answer :=
  assemble (prices x.2,x)

noncomputable def finishP {prices : Environment → Prices} (canon : Procedure envCode pricesCode prices) :
    Procedure argumentCode answerCode (finish prices) :=
  assembleP.comp ((canon.comp (second flowCode envCode)).pair (identity argumentCode))

end Output
end FlowMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI

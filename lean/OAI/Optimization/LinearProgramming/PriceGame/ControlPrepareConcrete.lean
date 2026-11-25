import OAI.Optimization.LinearProgramming.PriceGame.ControlPrepareSemantics
import OAI.Optimization.LinearProgramming.PriceGame.MarketClearMachine

/-! End-to-end numeric preparation on the recursive trial's packed input ABI. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
open ExactQuantumFactoring.BitStackProgram
open Trial Wire Market.InitializeMachine

/-- Numerical preparation reads its scratch globals as dimension, probe count,
and roster. The trial evaluator supplies the paper's fixed probe count. -/
def concretePrepare : PrepFrame → Prepared := prepareUsing clearMarket

noncomputable def concretePrepareP : Procedure (prodCode trialGlobalsCode trialCallDataCode)
    preparedCode concretePrepare := prepareUsingP clearP

theorem concretePrepare_eq (x : PrepFrame)
    (hw : x.1.1*2^x.2.1.level ≤ 2*(x.1.1*x.1.1))
    (hs : ∀ i < x.1.2.2.length, scoreTotal x.2.2 i ≤ scoreBudget x.1.1) :
    concretePrepare x = preparePacketSized x.1.1 x.1.2.1 x.1.2.2.length x.1.2.2 x.2.1 x.2.2 :=
  prepareUsing_agrees (fun I L => clear_eq I L) x hw hs

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

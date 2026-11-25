import OAI.Optimization.LinearProgramming.PriceGame.ControlEntryMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlReplayBox
import OAI.Optimization.LinearProgramming.OracleSpec.GuardedIteration

/-! Assemble the true stack instruction loop with input padding, chronological reply
consumption, and public query serialization. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
namespace Replay

open ExactQuantumFactoring.BitStackProgram Procedure

def initial (t : Tape) : State := live t.input.goods t.reverseReplies.reverse (.campaign
  (startCampaign t.input.goods t.input.range t.input.anchor.val (Campaign.rounds t.input.goods t.input.range)))

noncomputable def initialP : Procedure ecPad stateCode initial := by
  let n : Procedure eiPad unaryCode (fun i => i.goods) := unaryGoodsP.result (by intro _; rfl)
  let data := (n.comp tapeInputP).pair (replayRepliesP.pair (initialPCP.comp tapeInputP))
  exact ((prepend runningCode [false]).comp data).result (by intro _; rfl)

/-- A single fixed pure finite-stack program drives every event. Both polynomial
clocks are physically measured from the actual padded event tape. -/
noncomputable def dispatchOfProgram (solver : PublicSolver) {micro : ℕ × Driver.PC → Driver.Action}
    (stepP : Procedure (prodCode unaryCode Wire.combinedCode) Join.actionCode micro)
    (ticks width : Polynomial ℕ)
    (size : ∀ t j, j < ticks.eval (ecPad t).length →
      (stateCode ((advance micro)^[j] (initial t))).length ≤ width.eval (ecPad t).length)
    (correct : ∀ t, (advance micro)^[ticks.eval (ecPad t).length] (initial t) =
      Sum.inr (terminalResult (observe (solver t.input) t.reverseReplies.reverse))) :
    Procedure (OracleSpec.Dialogue.inputCode eiPad ecPad) (OracleSpec.Dialogue.actionCode ecPad)
      (dispatch solver) :=
  dialogueOfReplay _ (OracleSpec.Fuel.boundedReachable initialP (advanceP stepP) ticks width size) correct

end Replay
end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

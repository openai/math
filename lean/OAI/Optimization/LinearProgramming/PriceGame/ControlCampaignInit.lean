import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignTransition
import OAI.Optimization.LinearProgramming.PriceGame.CampaignRounds
import OAI.Optimization.LinearProgramming.PriceGame.OracleTrialCount

/-! # Cold start from the input tape, including the number of trials -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

/-- Compute the full campaign cursor from the padded public input alone, using
the given anchor, range, and the proved dimension/range-dependent trial count. -/
noncomputable def startFromPublicP : Procedure eiPad Wire.campaignCursorCode
    (fun i => startCampaign i.goods i.range i.anchor.val (Campaign.rounds i.goods i.range)) := by
  let n : Procedure eiPad unaryCode PublicInput.goods := unaryGoodsP.result (by intro i; rfl)
  let tail := (second Nat.bits (prodCode Nat.bits Nat.bits)).comp publicFieldsP
  let range := (first Nat.bits Nat.bits).comp tail
  let anchor := (second Nat.bits Nat.bits).comp tail
  let input := n.pair (range.pair (anchor.pair trialCountBinaryP))
  exact (startCampaignP.comp input).congrFun (by intro i; simp [Campaign.rounds_eq,Campaign.inputSize])

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

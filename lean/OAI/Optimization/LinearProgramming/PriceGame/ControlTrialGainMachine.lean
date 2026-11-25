import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialStepData
import OAI.Optimization.LinearProgramming.PriceGame.ControlRatListSum
import OAI.Optimization.LinearProgramming.PriceGame.LearningPackedTestMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlFeedbackMachine

/-! Physical rational dot products for the actual charged market allocation. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram Procedure
open Trial Wire TrialExecution

abbrev GainRow := Bool × List ℚ × List Bool
abbrev gainRowCode : GainRow → List Bool := prodCode boolCode (prodCode assemblyRowCode answerListCode)
def gainCell (row : GainRow) (i : ℕ) : ℚ :=
  atD row.2.1 i * labelSign row.1 * labelSign (atD row.2.2 i)

noncomputable def gainCellP : Procedure (prodCode unaryCode gainRowCode) ratCode (fun z => gainCell z.2 z.1) := by
  let idx := unaryToBits.comp (first unaryCode gainRowCode)
  let row := second unaryCode gainRowCode
  let sign := (ofBool ratCode labelSign).comp ((first boolCode (prodCode assemblyRowCode answerListCode)).comp row)
  let rest := (second boolCode (prodCode assemblyRowCode answerListCode)).comp row
  let qty := (atDP ratCode).comp (idx.pair ((first assemblyRowCode answerListCode).comp rest))
  let reply := (atDP boolCode).comp (idx.pair ((second assemblyRowCode answerListCode).comp rest))
  exact ratMul.comp ((ratMul.comp (qty.pair sign)).pair ((ofBool ratCode labelSign).comp reply))

def rowGain (n : ℕ) (row : GainRow) := ((List.range n).map (gainCell row)).sum
noncomputable def rowGainP : Procedure (prodCode unaryCode gainRowCode) ratCode (fun z => rowGain z.1 z.2) :=
  ratListSumP.comp (tabulate (f := gainCell) 0 gainCellP)

abbrev GainsInput := List PackedExpert × Prepared × List Bool
abbrev gainsInputCode : GainsInput → List Bool :=
  prodCode assemblyRosterCode (prodCode preparedCode answerListCode)

def expertGain (v : GainsInput) (e : ℕ) : ℚ :=
  if v.2.1.isProbe then rowGain v.2.1.baseline.length ((atD v.1 e).positive,atD v.2.1.allocation e,v.2.2) else 0

noncomputable def expertGainP : Procedure (prodCode unaryCode gainsInputCode) ratCode (fun z => expertGain z.2 z.1) := by
  let env := prodCode unaryCode gainsInputCode
  let idx := unaryToBits.comp (first unaryCode gainsInputCode)
  let data := second unaryCode gainsInputCode
  let roster := (first assemblyRosterCode (prodCode preparedCode answerListCode)).comp data
  let expert := (atDP packedExpertCode).comp (idx.pair roster)
  let tail := (second assemblyRosterCode (prodCode preparedCode answerListCode)).comp data
  let prep := (first preparedCode answerListCode).comp tail
  let labels := (second preparedCode answerListCode).comp tail
  let len := (rowSizeP ratCode 0).comp (preparedBaselineP.comp prep)
  let row := (atDP assemblyRowCode).comp (idx.pair (preparedAllocationP.comp prep))
  let pol := Learning.BitMachine.expertPositiveP.comp expert
  let gain := rowGainP.comp (len.pair (pol.pair (row.pair labels)))
  exact conditional (preparedKindP.comp prep) gain (constant env ratCode 0)

def packetGains (x : GainsInput) : List ℚ := (List.range x.1.length).map (expertGain x)
noncomputable def packetGainsP : Procedure gainsInputCode assemblyRowCode packetGains :=
  (tabulate (f := expertGain) 0 expertGainP).comp
    (((rowSizeP packedExpertCode default).comp (first assemblyRosterCode (prodCode preparedCode answerListCode))).pair
      (identity gainsInputCode))

/-- The returned packet contains the actual baseline, coordinatewise parent medians,
charged local gains, and the original completed child including its log. -/
def boundedChildReturn (experts : List PackedExpert) (prep : Prepared) (child : PackedRound) (labels : List Bool) :
    Completed := ⟨prep.baseline,medianRow prep.baseline child.prices,packetGains (experts,prep,labels),child⟩

abbrev childReturnCode := prodCode assemblyRosterCode (prodCode preparedCode (prodCode packedRoundCode answerListCode))
noncomputable def boundedChildReturnP : Procedure childReturnCode completedCode
    (fun x => boundedChildReturn x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let ex := first assemblyRosterCode (prodCode preparedCode (prodCode packedRoundCode answerListCode))
  let t := second assemblyRosterCode (prodCode preparedCode (prodCode packedRoundCode answerListCode))
  let prep := (first preparedCode (prodCode packedRoundCode answerListCode)).comp t
  let tail := (second preparedCode (prodCode packedRoundCode answerListCode)).comp t
  let child := (first packedRoundCode answerListCode).comp tail
  let labels := (second packedRoundCode answerListCode).comp tail
  let y := preparedBaselineP.comp prep
  let x := roundPricesP.comp child
  let mapped := medianRowP.comp (y.pair x)
  let gain := packetGainsP.comp (ex.pair (prep.pair labels))
  exact (y.pair (mapped.pair (gain.pair child))).result (by intro z; rfl)

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

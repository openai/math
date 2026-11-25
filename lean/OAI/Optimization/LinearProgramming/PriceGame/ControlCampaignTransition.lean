import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignFields
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignWeights
import OAI.Optimization.LinearProgramming.PriceGame.LearningBatchMachine

/-! # Physical outer transitions of the anchored price-game controller

The fixed polynomial score cap is computed from the input dimension in unary.
Every procedure admits a finite program and a polynomial bit cost on its encoded input.
-/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open Learning.GenerationCost Wire

abbrev RoundInput := ℕ × CampaignCursor × PackedRound
abbrev roundInputCode : RoundInput → List Bool := prodCode unaryCode (prodCode campaignCursorCode packedRoundCode)

/-- Dimension padding and an arbitrary old cursor and returned round. On all actual inputs
the public dimension equals that of the cursor. -/
def boundedFinish (x : RoundInput) : CampaignCursor :=
  let (n,c,r) := x
  let seen := c.state.seen ++ r.log
  let entries := c.state.population.experts ++ packedBatch n c.range seen
  let weights := clippedWeights ((2*n)^274,c.state.population.weights,r.scores)
  let pop : PackedPopulation := ⟨entries,nextWeights weights entries.length⟩
  let votes := c.state.positiveVotes + (if 0 < r.prices[c.anchor]?.getD 0 then 1 else 0)
  {c with left := c.left-1, state := ⟨pop,seen,votes⟩}

theorem boundedFinish_eq (c : CampaignCursor) (r : PackedRound)
    (bounded : ∀ i < c.state.population.weights.length, r.scores[i]?.getD 0 ≤ (2*c.dimension)^274) :
    boundedFinish (c.dimension,c,r) = finishRound c r := by
  simp only [boundedFinish,finishRound,acceptRound,advancePacked,clippedWeights_eq _ _ _ bounded]

private noncomputable def roundVoteP : Procedure (prodCode Nat.bits (listCode ratCode)) Nat.bits
    (fun x => if 0 < x.2[x.1]?.getD 0 then 1 else 0) := by
  let env := prodCode Nat.bits (listCode ratCode)
  let positive := OracleSpec.Arithmetic.ratLt.comp ((constant env ratCode (0 : ℚ)).pair (listGet ratCode 0))
  exact (conditional positive (constant env Nat.bits 1) (constant env Nat.bits 0)).congrFun
    (by intro x; simp)

noncomputable def finishRoundP : Procedure roundInputCode campaignCursorCode boundedFinish := by
  let dim := first unaryCode (prodCode campaignCursorCode packedRoundCode)
  let oldAndRound := second unaryCode (prodCode campaignCursorCode packedRoundCode)
  let cur := (first campaignCursorCode packedRoundCode).comp oldAndRound
  let rd := (second campaignCursorCode packedRoundCode).comp oldAndRound
  let state := stateP.comp cur
  let pop := statePopulationP.comp state
  let seen := (Procedure.listAppend packedProbeCode (default : PackedProbe)).comp ((seenP.comp state).pair (roundLogP.comp rd))
  let fresh := Learning.BitMachine.batchP.comp (dim.pair ((rangeP.comp cur).pair seen))
  let roster := (Procedure.listAppend packedExpertCode (default : PackedExpert)).comp ((rosterP.comp pop).pair fresh)
  let nr := (lengthUnaryP packedExpertCode (default : PackedExpert)).comp roster
  let scaled := clippedWeightsP.comp ((scoreCapP.comp dim).pair ((weightsP.comp pop).pair (roundScoresP.comp rd)))
  let weights := nextWeightsP.comp (nr.pair scaled)
  let nextPop := makePopulationP.comp (roster.pair weights)
  let vote := roundVoteP.comp ((anchorP.comp cur).pair (roundPricesP.comp rd))
  let votes := binaryAdd.comp ((votesP.comp state).pair vote)
  let nextState := makeStateP.comp (nextPop.pair (seen.pair votes))
  let left := binarySub.comp ((leftP.comp cur).pair (constant roundInputCode Nat.bits 1))
  exact makeCursorP.comp ((dimensionP.comp cur).pair ((rangeP.comp cur).pair ((anchorP.comp cur).pair
    ((totalP.comp cur).pair (left.pair nextState)))))

abbrev StartInput := ℕ × ℕ × ℕ × ℕ
abbrev startInputCode : StartInput → List Bool := prodCode unaryCode (prodCode Nat.bits (prodCode Nat.bits Nat.bits))

/-- Initial roster, empty observations, uniform rational weights, zero vote counter and
exactly the supplied numbers of total and remaining trials. -/
noncomputable def startCampaignP : Procedure startInputCode campaignCursorCode
    (fun x => startCampaign x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let n := first unaryCode (prodCode Nat.bits (prodCode Nat.bits Nat.bits))
  let nBits := unaryToBits.comp n
  let rest := second unaryCode (prodCode Nat.bits (prodCode Nat.bits Nat.bits))
  let range := (first Nat.bits (prodCode Nat.bits Nat.bits)).comp rest
  let tail := (second Nat.bits (prodCode Nat.bits Nat.bits)).comp rest
  let anchor := (first Nat.bits Nat.bits).comp tail
  let total := (second Nat.bits Nat.bits).comp tail
  let emptyLog := constant startInputCode seenCode ([] : List PackedProbe)
  let roster := Learning.BitMachine.batchP.comp (n.pair (range.pair emptyLog))
  let size := (lengthUnaryP packedExpertCode (default : PackedExpert)).comp roster
  let ratSize := natToRat.comp (unaryToBits.comp size)
  let unitWeight := ratDiv.comp ((constant startInputCode ratCode (1 : ℚ)).pair ratSize)
  let rowP := second unaryCode ratCode
  let rows := (tabulate (f := fun q : ℚ => fun _ : ℕ => q) 0 rowP).comp (size.pair unitWeight)
  let pop := makePopulationP.comp (roster.pair rows)
  let state := makeStateP.comp (pop.pair (emptyLog.pair (constant startInputCode Nat.bits 0)))
  let full := makeCursorP.comp (nBits.pair (range.pair (anchor.pair (total.pair (total.pair state)))))
  apply full.congrFun
  intro x
  change (⟨x.1,x.2.1,x.2.2.1,x.2.2.2,x.2.2.2,
      ⟨⟨packedBatch x.1 x.2.1 [],(List.range (packedBatch x.1 x.2.1 []).length).map
        (fun _ => (1 : ℚ) / (packedBatch x.1 x.2.1 []).length)⟩,[],0⟩⟩ : CampaignCursor) = _
  simp [startCampaign,initialPopulation]

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

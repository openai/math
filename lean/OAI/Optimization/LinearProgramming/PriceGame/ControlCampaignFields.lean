import OAI.Optimization.LinearProgramming.PriceGame.ControlAssemblyWire
import OAI.Optimization.LinearProgramming.PriceGame.ControlWireCampaign
import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic

/-! # Bit-stack field access and control tests for the campaign cursor -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open Wire

abbrev expertsCode := listCode packedExpertCode
abbrev weightsCode := listCode ratCode
abbrev scoresCode := listCode Nat.bits
abbrev seenCode := listCode packedProbeCode

private def ppFields (p : PackedPopulation) := (p.experts,p.weights)
noncomputable def rosterP : Procedure packedPopulationCode expertsCode PackedPopulation.experts :=
  (first expertsCode weightsCode).precompose ppFields
noncomputable def weightsP : Procedure packedPopulationCode weightsCode PackedPopulation.weights :=
  (second expertsCode weightsCode).precompose ppFields
noncomputable def makePopulationP : Procedure (prodCode expertsCode weightsCode) packedPopulationCode
    (fun x => ⟨x.1,x.2⟩) :=
  (identity (prodCode expertsCode weightsCode)).result (fun _ => rfl)

private def stFields (s : CampaignState) := (s.population,s.seen,s.positiveVotes)
noncomputable def statePopulationP : Procedure campaignStateCode packedPopulationCode CampaignState.population :=
  (first packedPopulationCode (prodCode seenCode Nat.bits)).precompose stFields
private noncomputable def stTail := (second packedPopulationCode (prodCode seenCode Nat.bits)).precompose stFields
noncomputable def seenP : Procedure campaignStateCode seenCode CampaignState.seen :=
  (first seenCode Nat.bits).comp stTail
noncomputable def votesP : Procedure campaignStateCode Nat.bits CampaignState.positiveVotes :=
  (second seenCode Nat.bits).comp stTail
abbrev stWords := prodCode packedPopulationCode (prodCode seenCode Nat.bits)
noncomputable def makeStateP : Procedure stWords campaignStateCode (fun x => ⟨x.1,x.2.1,x.2.2⟩) :=
  (identity stWords).result (fun _ => rfl)

private def curFields (c : CampaignCursor) := (c.dimension,c.range,c.anchor,c.total,c.left,c.state)
abbrev c1 := prodCode Nat.bits campaignStateCode
abbrev c2 := prodCode Nat.bits c1
abbrev c3 := prodCode Nat.bits c2
abbrev c4 := prodCode Nat.bits c3
abbrev curWords := prodCode Nat.bits c4

noncomputable def dimensionP : Procedure campaignCursorCode Nat.bits CampaignCursor.dimension :=
  (first Nat.bits c4).precompose curFields
private noncomputable def afterDimension := (second Nat.bits c4).precompose curFields
noncomputable def rangeP : Procedure campaignCursorCode Nat.bits CampaignCursor.range :=
  (first Nat.bits c3).comp afterDimension
private noncomputable def afterRange := (second Nat.bits c3).comp afterDimension
noncomputable def anchorP : Procedure campaignCursorCode Nat.bits CampaignCursor.anchor :=
  (first Nat.bits c2).comp afterRange
private noncomputable def afterAnchor := (second Nat.bits c2).comp afterRange
noncomputable def totalP : Procedure campaignCursorCode Nat.bits CampaignCursor.total :=
  (first Nat.bits c1).comp afterAnchor
private noncomputable def afterTotal := (second Nat.bits c1).comp afterAnchor
noncomputable def leftP : Procedure campaignCursorCode Nat.bits CampaignCursor.left :=
  (first Nat.bits campaignStateCode).comp afterTotal
noncomputable def stateP : Procedure campaignCursorCode campaignStateCode CampaignCursor.state :=
  (second Nat.bits campaignStateCode).comp afterTotal
noncomputable def makeCursorP : Procedure curWords campaignCursorCode
    (fun x => ⟨x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2.1,x.2.2.2.2.2⟩) :=
  (identity curWords).result (fun _ => rfl)

/-- The first bit gates the campaign/trial choice; the second bit is the strict majority. -/
noncomputable def boundaryBitsP : Procedure campaignCursorCode (prodCode boolCode boolCode)
    (fun c => (decide (c.left = 0), decide (c.total < 2*c.state.positiveVotes))) :=
  (binaryZero.comp leftP).pair (binaryLt.comp (totalP.pair (double.comp (votesP.comp stateP))))

theorem boundaryBits_correct (c : CampaignCursor) :
    campaignBoundary c =
    if decide (c.left = 0) then .halt (decide (c.total < 2*c.state.positiveVotes))
    else .needRound c.state.population c := by simp [campaignBoundary]

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

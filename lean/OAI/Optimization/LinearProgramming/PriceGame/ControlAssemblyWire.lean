import OAI.Optimization.LinearProgramming.PriceGame.ControlAssemblyValue
import OAI.Optimization.LinearProgramming.PriceGame.ControlWireTrial
import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCost
import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic

/-! Public word layouts for assembling one completed trial frame. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Trial Wire

abbrev assemblyRowCode := listCode ratCode
abbrev assemblyHistoryCode := listCode assemblyRowCode
abbrev assemblyLogCode := listCode packedProbeCode
abbrev assemblyRosterCode := listCode packedExpertCode
abbrev assemblyCallsCode := listCode completedCode

def assemblyFrameCode (x : AssemblyFrame) : List Bool :=
  prodCode assemblyRosterCode (prodCode nodeInputCode assemblyCallsCode) (x.experts, x.input, x.calls)

private def frameFields (x : AssemblyFrame) := (x.experts,x.input,x.calls)
private def inputFields (x : NodeInput) := (x.level,x.history,x.weights)
private def completedFields (x : Completed) := (x.baseline,x.mapped,x.gains,x.child)
private def roundFields (x : PackedRound) := (x.prices,x.scores,x.log)

noncomputable def frameRosterP : Procedure assemblyFrameCode assemblyRosterCode AssemblyFrame.experts :=
  (first assemblyRosterCode (prodCode nodeInputCode assemblyCallsCode)).precompose frameFields
private noncomputable def frameTail := (second assemblyRosterCode (prodCode nodeInputCode assemblyCallsCode)).precompose frameFields
noncomputable def frameInputP : Procedure assemblyFrameCode nodeInputCode AssemblyFrame.input :=
  (first nodeInputCode assemblyCallsCode).comp frameTail
noncomputable def frameCallsP : Procedure assemblyFrameCode assemblyCallsCode AssemblyFrame.calls :=
  (second nodeInputCode assemblyCallsCode).comp frameTail

noncomputable def nodeLevelP : Procedure nodeInputCode Nat.bits NodeInput.level :=
  (first Nat.bits (prodCode assemblyHistoryCode assemblyRowCode)).precompose inputFields
noncomputable def nodeHistoryP : Procedure nodeInputCode assemblyHistoryCode NodeInput.history :=
  (first assemblyHistoryCode assemblyRowCode).comp ((second Nat.bits (prodCode assemblyHistoryCode assemblyRowCode)).precompose inputFields)
noncomputable def nodeWeightsP : Procedure nodeInputCode assemblyRowCode NodeInput.weights :=
  (second assemblyHistoryCode assemblyRowCode).comp ((second Nat.bits (prodCode assemblyHistoryCode assemblyRowCode)).precompose inputFields)

private abbrev compTailCode := prodCode assemblyRowCode (prodCode assemblyRowCode packedRoundCode)
private noncomputable def cTail := (second assemblyRowCode compTailCode).precompose completedFields
private noncomputable def cMore := (second assemblyRowCode (prodCode assemblyRowCode packedRoundCode)).comp cTail

noncomputable def completedBaselineP : Procedure completedCode assemblyRowCode Completed.baseline :=
  (first assemblyRowCode compTailCode).precompose completedFields
noncomputable def completedMappedP : Procedure completedCode assemblyRowCode Completed.mapped :=
  (first assemblyRowCode (prodCode assemblyRowCode packedRoundCode)).comp cTail
noncomputable def completedGainsP : Procedure completedCode assemblyRowCode Completed.gains :=
  (first assemblyRowCode packedRoundCode).comp cMore
noncomputable def completedChildP : Procedure completedCode packedRoundCode Completed.child :=
  (second assemblyRowCode packedRoundCode).comp cMore

private noncomputable def roundTail :=
  (second assemblyRowCode (prodCode (listCode Nat.bits) assemblyLogCode)).precompose roundFields
noncomputable def roundPricesP : Procedure packedRoundCode assemblyRowCode PackedRound.prices :=
  (first assemblyRowCode (prodCode (listCode Nat.bits) assemblyLogCode)).precompose roundFields
noncomputable def roundScoresP : Procedure packedRoundCode (listCode Nat.bits) PackedRound.scores :=
  (first (listCode Nat.bits) assemblyLogCode).comp roundTail
noncomputable def roundLogP : Procedure packedRoundCode assemblyLogCode PackedRound.log :=
  (second (listCode Nat.bits) assemblyLogCode).comp roundTail

/-- A charged access uses the canonical list walk, with the same default on a short list. -/
noncomputable def atDP {α : Type} [Inhabited α] (ea : α → List Bool) :
    Procedure (prodCode Nat.bits (listCode ea)) ea (fun p => atD p.2 p.1) := by
  apply (listGet ea default).congrFun
  intro p
  simp [atD, List.head?_drop]

/-- Extract a list prefix using ordinary binary subtraction and two reversals.
The intermediate arrays never exceed the original list. -/
noncomputable def takeListP {α : Type} (ea : α → List Bool) (d : α) :
    Procedure (prodCode Nat.bits (listCode ea)) (listCode ea) (fun p => p.2.take p.1) := by
  let size := (listLength ea d).comp (second Nat.bits (listCode ea))
  let n := first Nat.bits (listCode ea)
  let left := binarySub.comp (size.pair n)
  let xs := (listReverse ea d).comp (second Nat.bits (listCode ea))
  let q := (listReverse ea d).comp ((listDrop ea).comp (left.pair xs))
  apply q.congrFun
  intro p
  change (p.2.reverse.drop (p.2.length - p.1)).reverse = p.2.take p.1
  rw [← List.reverse_take, List.reverse_reverse]

noncomputable def frameFirstP (r : ℕ) : Procedure assemblyFrameCode assemblyCallsCode (fun x => x.calls.take r) :=
  (takeListP completedCode default).comp ((constant assemblyFrameCode Nat.bits r).pair frameCallsP)

noncomputable def frameFinalP (r : ℕ) : Procedure assemblyFrameCode assemblyCallsCode (finalRows r) :=
  (listDrop completedCode).comp ((constant assemblyFrameCode Nat.bits r).pair frameCallsP)

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.PriceGame.ControlAssemblyWire

/-! Charged table scans for the columns and chronological log of an assembled frame. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Learning.GenerationCost Trial Wire

/-- Read one column of a row field from a completed-call list. Each access physically
walks the framed list at the given index. -/
noncomputable def columnP {α : Type} [Inhabited α] (ea : α → List Bool)
    {field : Completed → List α} (getField : Procedure completedCode (listCode ea) field) :
    Procedure (prodCode assemblyCallsCode Nat.bits) (listCode ea)
      (fun p => p.1.map fun c => atD (field c) p.2) := by
  let cell := (atDP ea).comp ((second completedCode Nat.bits).pair
    (getField.comp (first completedCode Nat.bits)))
  exact mapContextP default default cell

/-- Unary price count obtained by reading the first final row. -/
noncomputable def outputWidthP (r : ℕ) : Procedure assemblyFrameCode unaryCode (outputWidth r) :=
  (lengthUnaryP ratCode 0).comp (completedMappedP.comp
    ((listHead completedCode default).comp (frameFinalP r)))

noncomputable def outputRosterLengthP : Procedure assemblyFrameCode unaryCode
    (fun x => x.experts.length) :=
  (lengthUnaryP packedExpertCode default).comp frameRosterP

/-- Extract just the final mapped prices for the queried coordinate. -/
noncomputable def finalColumnP (r : ℕ) : Procedure (prodCode unaryCode assemblyFrameCode) assemblyRowCode
    (fun p => (finalRows r p.2).map fun c => atD c.mapped p.1) :=
  (columnP ratCode completedMappedP).comp
    (((frameFinalP r).comp (second unaryCode assemblyFrameCode)).pair
      (unaryToBits.comp (first unaryCode assemblyFrameCode)))

noncomputable def gainColumnP (r : ℕ) : Procedure (prodCode unaryCode assemblyFrameCode) assemblyRowCode
    (fun p => (p.2.calls.take r).map fun c => atD c.gains p.1) :=
  (columnP ratCode completedGainsP).comp
    (((frameFirstP r).comp (second unaryCode assemblyFrameCode)).pair
      (unaryToBits.comp (first unaryCode assemblyFrameCode)))

noncomputable def scoreColumnP : Procedure (prodCode unaryCode assemblyFrameCode) (listCode Nat.bits)
    (fun p => p.2.calls.map fun c => atD c.child.scores p.1) :=
  (columnP Nat.bits (roundScoresP.comp completedChildP)).comp
    ((frameCallsP.comp (second unaryCode assemblyFrameCode)).pair (unaryToBits.comp (first unaryCode assemblyFrameCode)))

/-- Rebuild each first-group observation from its returned market price and the supplied
node history, and append its original child log. -/
noncomputable def oneProbeLogP : Procedure (prodCode completedCode nodeInputCode) assemblyLogCode
    (fun p => (⟨p.2.level,p.1.baseline,p.2.history⟩ : PackedProbe) :: p.1.child.log) := by
  let row := first completedCode nodeInputCode
  let node := second completedCode nodeInputCode
  let log := roundLogP.comp (completedChildP.comp row)
  let data := (nodeLevelP.comp node).pair ((completedBaselineP.comp row).pair (nodeHistoryP.comp node))
  let obs : Procedure (prodCode completedCode nodeInputCode) packedProbeCode
      (fun p => (⟨p.2.level,p.1.baseline,p.2.history⟩ : PackedProbe)) := data.result (fun _ => rfl)
  exact (listCons packedProbeCode).comp (obs.pair log)

noncomputable def frameLogP (r : ℕ) : Procedure assemblyFrameCode assemblyLogCode (frameLog r) := by
  let probeLogs := (mapContextP default [] oneProbeLogP).comp ((frameFirstP r).pair frameInputP)
  let finalLog := roundLogP.comp completedChildP
  let finalLogs := (listMap default [] finalLog).comp (frameFinalP r)
  let flatten := flattenP packedProbeCode default
  exact (listAppend packedProbeCode default).comp
    ((flatten.comp probeLogs).pair (flatten.comp finalLogs))

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialStepWire
import OAI.Optimization.LinearProgramming.PriceGame.ControlAssemblyWire
import OAI.Optimization.LinearProgramming.PriceGame.ControlScanMachine
import OAI.Computability.QuantumFactoring.BitStackFold

/-! Numeric packet operations used independently of the adaptive control logic. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram Procedure
open Trial Wire

private abbrev preparedTail := prodCode assemblyRowCode (prodCode assemblyHistoryCode assemblyRowCode)
private def preparedFields (p : Prepared) := (p.isProbe,p.baseline,p.allocation,p.deepWeights)

noncomputable def preparedKindP : Procedure preparedCode boolCode Prepared.isProbe :=
  (first boolCode preparedTail).precompose preparedFields
private noncomputable def prepTailP := (second boolCode preparedTail).precompose preparedFields
noncomputable def preparedBaselineP : Procedure preparedCode assemblyRowCode Prepared.baseline :=
  (first assemblyRowCode (prodCode assemblyHistoryCode assemblyRowCode)).comp prepTailP
private noncomputable def prepBothP := (second assemblyRowCode (prodCode assemblyHistoryCode assemblyRowCode)).comp prepTailP
noncomputable def preparedAllocationP : Procedure preparedCode assemblyHistoryCode Prepared.allocation :=
  (first assemblyHistoryCode assemblyRowCode).comp prepBothP
noncomputable def preparedDeepP : Procedure preparedCode assemblyRowCode Prepared.deepWeights :=
  (second assemblyHistoryCode assemblyRowCode).comp prepBothP

/-- Push the solved baseline onto chronological history and install the actual deep row. -/
noncomputable def descendFieldsP : Procedure (prodCode nodeInputCode preparedCode) nodeInputCode
    (fun x => descend x.1 x.2) := by
  let env := prodCode nodeInputCode preparedCode
  let i := first nodeInputCode preparedCode
  let p := second nodeInputCode preparedCode
  let n := successor.comp (nodeLevelP.comp i)
  let singleton := (listCons assemblyRowCode).comp ((preparedBaselineP.comp p).pair (constant env assemblyHistoryCode []))
  let rows := (listAppend assemblyRowCode []).comp ((nodeHistoryP.comp i).pair singleton)
  exact (n.pair (rows.pair (preparedDeepP.comp p))).result (by intro x; rfl)

noncomputable def trialDescendP :
    Procedure (prodCode trialGlobalsCode (prodCode nodeInputCode preparedCode)) nodeInputCode
      (fun x => descend x.2.1 x.2.2) :=
  descendFieldsP.comp (second trialGlobalsCode (prodCode nodeInputCode preparedCode))

private noncomputable def pushAnswer (b : Bool) : Procedure answerListCode answerListCode (fun xs => b::xs) :=
  (listCons boolCode).comp ((constant answerListCode boolCode b).pair (identity answerListCode))

private theorem pushLength (b : Bool) (s : List Bool) :
    (answerListCode (b::s)).length ≤ (answerListCode s).length + 4 := by
  change (listCode boolCode (b::s)).length ≤ (listCode boolCode s).length + 4
  rw [listCode_length_cons]
  change 2*1+2+_ ≤ _+4
  omega

private theorem foldPush (s acc : List Bool) :
    s.foldl (bitAction (fun a => false::a) (fun a => true::a)) acc = s.reverse++acc := by
  induction s generalizing acc with
  | nil => rfl
  | cons b tail ih =>
    rw [List.foldl_cons, ih, List.reverse_cons, List.append_assoc]
    cases b <;> rfl

/-- The saved frame uses unframed reply bits. The scanner consumes the canonical
framed list of single-bit words; both traversals and temporary space are metered. -/
noncomputable def frameRepliesP : Procedure (id : List Bool → List Bool) answerListCode id := by
  let loop := foldBitsLinear (pushAnswer false) (pushAnswer true) 4 (pushLength false) (pushLength true)
  let init := (identity (id : List Bool → List Bool)).pair (constant id answerListCode [])
  apply ((listReverse boolCode false).comp (loop.comp init)).congrFun
  intro bs
  change (bs.foldl (bitAction (fun a => false::a) (fun a => true::a)) []).reverse = bs
  rw [foldPush,List.append_nil,List.reverse_reverse]

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.PriceGame.ControlPrepareWeightsMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlPrepareBudget
import OAI.Optimization.LinearProgramming.PriceGame.ControlPrepareBids
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialStepWire

/-! Charged reconstruction of row weights and score fuel from the suspended trial. -/
set_option exponentiation.threshold 2048
set_option maxRecDepth 4000

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
open ExactQuantumFactoring.BitStackProgram Procedure
open Trial Wire

abbrev PrepFrame := TrialGlobals × (NodeInput × List Completed)
abbrev prepFrameCode : PrepFrame → List Bool := prodCode trialGlobalsCode trialCallDataCode
noncomputable abbrev prepGlobalsP := first trialGlobalsCode trialCallDataCode
noncomputable abbrev prepDataP := second trialGlobalsCode trialCallDataCode
noncomputable abbrev prepNP := (first unaryCode (prodCode Nat.bits assemblyRosterCode)).comp prepGlobalsP
noncomputable abbrev prepOtherP := (second unaryCode (prodCode Nat.bits assemblyRosterCode)).comp prepGlobalsP
noncomputable abbrev prepRP := (first Nat.bits assemblyRosterCode).comp prepOtherP
noncomputable abbrev prepRosterP := (second Nat.bits assemblyRosterCode).comp prepOtherP
noncomputable abbrev prepNodeP := (first nodeInputCode assemblyCallsCode).comp prepDataP
noncomputable abbrev prepCallsP := (second nodeInputCode assemblyCallsCode).comp prepDataP
noncomputable abbrev prepLevelP := nodeLevelP.comp prepNodeP
noncomputable abbrev prepHistoryP := nodeHistoryP.comp prepNodeP
noncomputable abbrev prepWeightP := nodeWeightsP.comp prepNodeP
noncomputable abbrev prepCountP := (rowSizeP packedExpertCode default).comp prepRosterP

private abbrev weightCellCode := prodCode unaryCode prepFrameCode
private noncomputable abbrev wcIndex := unaryToBits.comp (first unaryCode prepFrameCode)
private noncomputable abbrev wcFrame := second unaryCode prepFrameCode
private noncomputable abbrev wcExpert := (atDP packedExpertCode).comp (wcIndex.pair (prepRosterP.comp wcFrame))
private noncomputable abbrev wcLocal := natEqP.comp ((Learning.BitMachine.expertLevelP.comp wcExpert).pair
  (prepLevelP.comp wcFrame))
private noncomputable abbrev wcOld := (atDP ratCode).comp (wcIndex.pair (prepWeightP.comp wcFrame))
private noncomputable abbrev wcZero := constant weightCellCode ratCode (0:ℚ)

def prepLocalCell (x : PrepFrame) (i : ℕ) : ℚ :=
  localWeightRaw x.2.2 i (if (atD x.1.2.2 i).level = x.2.1.level then atD x.2.1.weights i else 0)

def prepDeepCell (x : PrepFrame) (i : ℕ) : ℚ :=
  deepCapped (machineBudget x.1.1) x.2.2 i
    (if (atD x.1.2.2 i).level = x.2.1.level then 0 else atD x.2.1.weights i)

noncomputable def prepLocalCellP : Procedure weightCellCode ratCode (fun p => prepLocalCell p.2 p.1) := by
  let init := conditional wcLocal wcOld wcZero
  exact (localWeightRawP.comp (wcIndex.pair ((prepCallsP.comp wcFrame).pair init))).congrFun (by
    intro p
    simp [prepLocalCell, Function.comp_def])

noncomputable def prepDeepCellP : Procedure weightCellCode ratCode (fun p => prepDeepCell p.2 p.1) := by
  let init := conditional wcLocal wcZero wcOld
  let packet := wcIndex.pair ((prepCallsP.comp wcFrame).pair init)
  exact (deepWeightRawP.comp ((machineBudgetP.comp (prepNP.comp wcFrame)).pair packet)).congrFun (by
    intro p
    simp [prepDeepCell, Function.comp_def])

def prepLocalRow (x : PrepFrame) : List ℚ := (List.range x.1.2.2.length).map (prepLocalCell x)
def prepDeepRow (x : PrepFrame) : List ℚ := (List.range x.1.2.2.length).map (prepDeepCell x)

noncomputable def prepLocalRowP : Procedure prepFrameCode assemblyRowCode prepLocalRow :=
  (tabulate (f := prepLocalCell) (0:ℚ) prepLocalCellP).comp (prepCountP.pair (identity prepFrameCode))

noncomputable def prepDeepRowP : Procedure prepFrameCode assemblyRowCode prepDeepRow := by
  let row := tabulate (ea := prepFrameCode) (eb := ratCode) (f := prepDeepCell) (0:ℚ) prepDeepCellP
  exact (row.comp (prepCountP.pair (identity prepFrameCode))).congrFun (fun _ => rfl)

theorem prepDeepRow_eq (x : PrepFrame)
    (hs : ∀ i < x.1.2.2.length, scoreTotal x.2.2 i ≤ scoreBudget x.1.1) :
    prepDeepRow x = deepWeightsSized x.1.2.2.length x.1.2.2 x.2.1 x.2.2 := by
  apply List.ext_getElem
  · simp [prepDeepRow, deepWeightsSized]
  · intro i h₁ _
    have hi : i < x.1.2.2.length := by simpa [prepDeepRow] using h₁
    simp only [prepDeepRow, List.getElem_map, List.getElem_range, deepWeightsSized, List.getElem_ofFn]
    exact deepCapped_eq x.2.2 i _ ((hs i hi).trans (scoreBudget_le_machineBudget x.1.1))

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

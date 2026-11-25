import OAI.Hierarchy.DescentScheduledResetAtPorts
import OAI.Hierarchy.DescentDatedSavedRotation

namespace OAI
/-! # The saved rotation matrix belongs to the reset that issued it -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.AtPorts
open DescentSixParty.PackedFlow.Canvas DescentPackedFlowPublication DescentSIMDLookup
noncomputable section

theorem saved_between {F Pin : Type} [Field F] (a : AtPorts) :
    a.floor≤(NativeDate.reset (F:=F) (P:=Pin) a.inner).saved a.priorStart ∧
    (NativeDate.reset (F:=F) (P:=Pin) a.inner).saved a.priorStart<a.fullEnd := by
  let v:=a.inner
  let entry:=v.stageStart a.priorStart
  let chart:=v.chart entry
  let code:=NativeDate.reset (F:=F) (P:=Pin) v
  let loc:=code.saved a.priorStart
  have passed : a.priorStart≤entry:=v.ingress.after _
  have cuts:=v.occupied entry
  have range:=chart.estimator_range v.payload v.gain v.positive
  change chart.endAddress≤_ ∧ _≤_ ∧ _≤chart.remixEnd v.payload v.gain v.positive at range
  have before : entry ≤ chart.remixEnd v.payload v.gain v.positive :=
    cuts.1.trans ((range.1.trans range.2.1).trans range.2.2)
  have saved : chart.remixEnd v.payload v.gain v.positive≤loc := by
    change _≤chart.remixEnd v.payload v.gain v.positive+_+_
    omega
  have next : loc+1=chart.rotationEnd v.payload v.gain v.positive :=
    NativeDate.saved_succ code a.priorStart
  have upper : chart.rotationEnd v.payload v.gain v.positive≤v.rebased entry := by
    unfold PhysicalReset.rebased Placement.repackedEnd Subwords.finish Subwords.destination
    dsimp only [chart]
    omega
  exact ⟨(((a.stages.1.trans passed).trans before).trans saved),
    Nat.lt_of_succ_le (next.le.trans (upper.trans cuts.2.2))⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.AtPorts

end OAI

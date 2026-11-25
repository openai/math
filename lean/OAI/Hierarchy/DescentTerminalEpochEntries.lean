import OAI.Hierarchy.DescentTerminalObservedPins
import OAI.Hierarchy.DescentTerminalSeedSelectors
import OAI.Hierarchy.DescentSeedProjection
import OAI.Hierarchy.DescentTerminalBundleMenu

namespace OAI
/-! # Seed scalar multiplicities and terminal operand rows on the actual chosen epoch -/
namespace Hierarchy.DescentTerminalReadout
open Catalyst Computability.BorderVNP.Crossing DescentInitialHost DescentSixParty
open DescentSeedRoot DescentTerminalPorts DescentTerminalBundleMenu
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {k pins : ℕ} (X : Approximation F k pins) (R s : ℕ)
    {u ε : ℝ} (G : PoweredGadget F) (hu : 0≤u) (he : 0≤ε) {J h C Ht t : ℕ}
    (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J (initialGroup X R s))
local notation "P" => Fin (Fintype.card (Catalyst.Port pins X.width))
local notation "original" => DescentSeedRoot.originalScalar X (R:=R)

def seedCount (c : (Epochs.finish G hu he run).Choice) := DescentSeedRoot.selected X (Epochs.seedChoice G hu he run c)

theorem epoch_weight (c : (Epochs.finish G hu he run).Choice) :
    (Epochs.finish G hu he run).weight c=∏i:CountKey X R,(original i)^(seedCount X R s G hu he run c i) :=
  (Epochs.weight_initial G hu he _ run c).trans (DescentSeedRoot.original_weight X _)

/-- The indexed requests are the real repeated seed coefficients and
one request per packed slot. They never include the failure scalar. -/
theorem epoch_entries (c : (Epochs.finish G hu he run).Choice) {localBins slots : ℕ} (menu : Fin localBins→F) (keys : Fin slots→Fin localBins)
    (outer : Ports (fun _:Σ _j : Fin R,P=>s*1)) (a : ((Epochs.finish G hu he run).state c).graph.Assignment)
    (rowValues : (∏j,menu (keys j))=∏v,((Epochs.finish G hu he run).state c).graph.read ((Epochs.finish G hu he run).state c).tables a outer v) :
    (∏j,scalar original menu (requests (seedCount X R s G hu he run c) keys j))=
      (Epochs.finish G hu he run).weight c*∏v,((Epochs.finish G hu he run).state c).graph.read ((Epochs.finish G hu he run).state c).tables a outer v := by
  rw [requests_eval,rowValues,epoch_weight]

end
end Hierarchy.DescentTerminalReadout

end OAI

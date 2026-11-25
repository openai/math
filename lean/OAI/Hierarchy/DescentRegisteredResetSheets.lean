import OAI.Hierarchy.DescentRegisteredLocalSheets
import OAI.Hierarchy.DescentRegisteredRankedSheetCharge
import OAI.Hierarchy.DescentRegisteredControlSheet
import OAI.Hierarchy.DescentRegisteredSevenTariff
import OAI.Hierarchy.DescentRegisteredPacketSheets
import OAI.Hierarchy.DescentRegisteredResetSum

namespace OAI
/-! All six native costs of the reset candidate and operand sheets at the registered date. -/
namespace Hierarchy.DescentSixParty.RegisteredReset
open DescentCompiler TerminalScale Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (K : Parameters)

theorem sheets (saving : ℕ) : Region G board op K 8 saving:=by
  apply of_sum G board op K 8 saving (fun a=>a.sheetCost) (fun a g=>a.sheets_paid g)
  intro j
  fin_cases j
  · exact local_sheet G board op K false saving
  · exact ranked_sheet_charge G board op K saving
  · exact control_sheet G board op K saving
  · exact seven_sheet G board op K saving
  · exact local_sheet G board op K true saving
  · obtain ⟨lead,exponent,paid⟩:=packet_sheet G board op K saving
    refine ⟨lead,exponent,1,0,?_⟩
    intro τ B _ den _ _
    filter_upwards [paid τ B den] with h price
    intro a g _ J
    let plan:=a.hardware.inner
    let start:=plan.rebased (plan.stageStart a.hardware.priorStart)
    rw [one_mul]
    change a.packetInvoice (plan.successor.operandFloor start)*a.w ≤ _
    exact price a g (plan.successor.operandFloor start)

end
end Hierarchy.DescentSixParty.RegisteredReset

end OAI

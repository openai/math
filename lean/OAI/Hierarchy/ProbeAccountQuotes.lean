import OAI.Hierarchy.ProbePublicPrices
import OAI.Hierarchy.ProtocolRAMCalendarNativeAccounts
import OAI.Hierarchy.ProtocolRAMCalendarRouteBox

namespace OAI
/-! # The actual calendar account maximizer reads the stock addressed by the price ROM -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe PurchaseCT
open scoped BigOperators Classical
noncomputable section

/-- At every actual attempt program point, the economic maximizer equals the quote
computed on the current native memory. The chronology selects the previous published
stock base and each typed commodity uses its own immutable row offset. -/
theorem native_account_quotes {z d k q goods w : ℕ} (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods)
    (initial payload precision : ℕ) (billed : Event→WordRows) (cash a M W T s : ℝ)
    (atStep : Attempt) (snapshot : Memory w) :
    let N := CoreBoard.Stages z d
    let A := nativeAccounts (N:=N) c arena format initial payload billed cash a M
      (W⁻¹^4/(N*T^2)) (routeCap N M)
    let base := previousStock c initial (publishedStock c arena format) (.attempt atStep)
    maximizer A.a A.M s A.coefficient A.box (A.bank.units payload (A.read atStep snapshot)) =
      stageQuotes (publicPhase (2*rounds d+1) a M W T s payload precision) 0 1 base snapshot := by
  dsimp only
  have count : CoreBoard.Stages z d=2*rounds d+1 := template_length ..
  funext i
  change offer a (bonus (W⁻¹^4/(CoreBoard.Stages z d*T^2)) i) M s
    (((snapshot (stockAt c arena format initial atStep i)).val:ℝ)/payload)
    (routeCap (CoreBoard.Stages z d) M (PurchaseInventory.lane i)) = _
  rw [routeCap_named]
  rcases i with p|⟨⟨p,t⟩,j⟩
  · simp [bonus,CoreBoard.commodityLength,stageQuotes,stockQuotes,PhasePrice.quote,publicPhase,PurchaseInventory.stock,
      stockAt,PurchaseInventory.slot,PurchaseInventory.lane,PurchaseInventory.record,count]
  · simp [bonus,CoreBoard.commodityLength,stageQuotes,stockQuotes,PhasePrice.quote,publicPhase,PurchaseInventory.stock,
      stockAt,PurchaseInventory.slot,PurchaseInventory.record,PurchaseInventory.lane,stageNumber,Fin.cast,count]

end
end Hierarchy.ProtocolRAM.Calendar

end OAI

import OAI.Hierarchy.TaggedWideSparseOrdinal
import OAI.Hierarchy.TaggedWireDistinctChords

namespace OAI
/-! # Agreement of the native and chronological order on parallel wires -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRows
open WireTelescope AdaptiveProbe ProtocolRAM ProtocolRAM.Calendar.CatalogueRows RoleProgram
open scoped Classical
variable {h W k attempts : ℕ} (S:PurchaseSampler) (π:Equiv.Perm (Fin (2^h)))
    (depth:ℕ) (mark:ReportSockets.Marks h W k attempts) (b:Board)
    (order:Fin b.coreRows≃Edges S h (2^W) k)
    (size:attempts*(ProtocolRAM.PurchaseFrozen.count h (2^W) k*ProtocolRAM.PurchaseFrozen.paths h S.degree depth)=b.boughtRows)
    {axes:ℕ} (a:Catalysts h W k≃Fin axes)
local notation "names" => timeRows S π depth mark b order size a
local notation "address" => raw S π depth mark b order size names
local notation "ch" => HistoryRoles.sorted S π depth mark

theorem earlier_on_chord (i j:Fin (Fintype.card (Source S π depth mark)))
    (same:ch (names i)=ch (names j)) :
    i<j ↔ address i<address j :=
  (time_before S π depth mark b order size a i j).trans
    (terminal_order_on_chord S π depth mark b order size
      (PurchaseInventory.slotEquiv h (Stages h (2^W)) k) a
      (sorted_goods_injective S π depth mark) (sorted_catalysts_injective S π depth mark)
      (names i) (names j) same)

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRows
end

end OAI

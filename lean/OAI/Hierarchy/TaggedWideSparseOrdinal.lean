import OAI.Hierarchy.TaggedWideDatedRows
import OAI.Hierarchy.TaggedWideOrdinalComparison

namespace OAI
/-! # The chronological and terminal ordinal comparisons within each chord -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRows
open WireTelescope AdaptiveProbe ProtocolRAM ProtocolRAM.Calendar.CatalogueRows RoleProgram ReportSockets
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical
variable {h W k attempts : ℕ} (S:PurchaseSampler) (π:Equiv.Perm (Fin (2^h)))
    (depth:ℕ) (mark:ReportSockets.Marks h W k attempts) (b:Board)
    (order:Fin b.coreRows≃Edges S h (2^W) k)
    (size:attempts*(ProtocolRAM.PurchaseFrozen.count h (2^W) k*ProtocolRAM.PurchaseFrozen.paths h S.degree depth)=b.boughtRows)
    {ng na:ℕ} (g:Goods h W k≃Fin ng) (a:Catalysts h W k≃Fin na)
local notation "Src" => Source S π depth mark
local notation "key" => sparseKey S π depth mark b order size g a
local notation "original" => embed S π depth mark b order size
local notation "o" => SettledMatrix.Layout.ordinal (r:=b.rows) (I:=Goods h W k) (A:=Catalysts h W k)
local notation "E" => b.ordinal S π depth mark order size
local notation "c" => HistoryRoles.sorted S π depth mark

theorem terminal_order_on_chord
    (goods : Function.Injective (fun z:Goods h W k=>c (.inr (.inl z))))
    (reserve : Function.Injective (fun z:Catalysts h W k=>c (.inr (.inr z))))
    (i j:Src) (same:c i=c j) :
    key i<key j ↔ o (original i)<o (original j) := by
  have read (i:Src) : (key i).val=SettledMatrix.Layout.blockValue E g a i := by
    rcases i with i|i|i
    · exact key_paid S π depth mark b order size g a i
    · exact key_goods S π depth mark b order size g a i
    · exact key_reserve S π depth mark b order size g a i
  change (key i).val<(key j).val ↔ _
  rw [read,read]
  exact SettledMatrix.Layout.block_order_on_chord E g a c goods reserve i j same

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRows
end

end OAI

import OAI.Hierarchy.TaggedWireRoleInventory
import OAI.Hierarchy.ProtocolRAMCatalystReserveBits

namespace OAI
/-! # The checked native settlement determines the original catalogue widths -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
open AdaptiveProbe ProtocolRAM Calendar CatalystArchive WireTelescope
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators
variable {h W k edges payload word : ℕ}
local notation "K" => Fintype.card (Columns h (2^W))*k
local notation "N" => Fintype.card (Old h W k edges)

/-- The original signed role matrix uses the same paid counters, remaining
commodity bank and ordered catalyst debits as the terminal reconciliation. -/
theorem settled_width (base : ℕ) (m : Memory word) (paid active : Bank) (b : RouteSettlement.Banks)
    (read : StockResident (h:=h) (W:=W) (k:=k) (edges:=edges) base m)
    (wide : 2<2^word) (room : N≤2^word)
    (mesh : Mesh) (issued : Attempt→Entry K payload)
    (counters : ∀j : Fin K,
      RouteSettlement.actual b.used m j.val=usedAt (CatalystArchive.site mesh issued) (debit mesh issued) j ∧
      RouteSettlement.actual b.reserved m j.val=fuel mesh*payload)
    (r : Fin N) :
    ((Inventory.ofOriginal base N paid active b.reserved b.used).width.eval m (r.val:Word word)).val =
      match SettledMatrix.Layout.numbered (r:=edges) (I:=Goods h W k) (A:=Catalysts h W k) r with
      | .inl p => (paid.read m (p.val:Word word)).val
      | .inr (.inl i) => (active.read m ((PurchaseInventory.slot i:ℕ):Word word)).val
      | .inr (.inr c) => fuel mesh*payload-usedAt (CatalystArchive.site mesh issued) (debit mesh issued)
          (pairKeys (Columns h (2^W)) k c) := by
  have covered (c : Catalysts h W k) :
      let j := pairKeys (Columns h (2^W)) k c
      (b.used.read m (j.val:Word word)).val≤(b.reserved.read m (j.val:Word word)).val := by
    let j := pairKeys (Columns h (2^W)) k c
    change RouteSettlement.actual b.used m j.val≤RouteSettlement.actual b.reserved m j.val
    rw [(counters j).1,(counters j).2]
    exact funded mesh issued j
  rw [stock_width base m paid active b.reserved b.used read wide room covered r]
  rcases SettledMatrix.Layout.numbered (r:=edges) (I:=Goods h W k) (A:=Catalysts h W k) r with p|i|c
  · rfl
  · rfl
  · let j := pairKeys (Columns h (2^W)) k c
    change RouteSettlement.actual b.reserved m j.val-RouteSettlement.actual b.used m j.val=_
    rw [(counters j).2,(counters j).1]

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
end

end OAI

import OAI.Hierarchy.TaggedWireRoleInventory

namespace OAI
/-! # The signed role and inventory operands through the concrete prefix replay -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
open AdaptiveProbe ReportSockets ProtocolRAM TaggedShorterSupergroups WireTelescope
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {h W k attempts H R w edges : ℕ} (S : PurchaseSampler)
variable (order : Fin R≃Edges S h (2^W) k)
variable (dir : Directory (reserved h W (copies k attempts)) H)
local notation "N" => Fintype.card (Old h W k edges)

theorem after_replay (edges start : ℕ) {m final : Memory w}
    (roles : (tables S order dir edges).Resident start m)
    (geometry : SiteROM.Resident dir ((shape (R:=R) S dir edges).offset start) m)
    (stock : StockResident (h:=h) (W:=W) (k:=k) (edges:=edges) ((shape (R:=R) S dir edges).stop start) m)
    (keep : ∀u,u < (shape (R:=R) S dir edges).ceiling start → final u=m u) :
    let z := shape (R:=R) S dir edges
    (tables S order dir edges).Resident start final ∧ SiteROM.Resident dir (z.offset start) final ∧
      StockResident (h:=h) (W:=W) (k:=k) (edges:=edges) (z.stop start) final := by
  let z := shape (R:=R) S dir edges
  have stop : z.offset start≤z.stop start := Nat.le_add_right ..
  have size : z.stop start+2*z.old≤z.ceiling start := by
    have span : z.old≤ProtocolRAMPurchaseSampler.span z.old := (ProtocolRAMPurchaseSampler.lt_span _).le
    have bank := stock_room (R:=R) S dir edges start
    change z.stop start+z.old+ProtocolRAMPurchaseSampler.span z.old≤z.ceiling start at bank
    omega
  have upper : z.stop start ≤ z.ceiling start := (Nat.le_add_right _ _).trans size
  refine ⟨Tables.Resident.frame _ roles (fun u _ hi=>keep u ((hi.trans_le stop).trans_le upper)),?_,?_⟩
  · apply geometry.frame
    intro u _ hi
    change u < z.stop start at hi
    exact keep u (hi.trans_le upper)
  · apply stock.frame
    intro u _ hi
    change u < z.stop start + 2*z.old at hi
    exact keep u (hi.trans_le size)

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
end

end OAI

import OAI.Hierarchy.TaggedWideDatedRoleInput
import OAI.Hierarchy.ProbeFixedWideGoods
import OAI.Hierarchy.ProbeFixedStockWindow
import OAI.Hierarchy.ProbeFixedStripCounts
import OAI.Hierarchy.ProtocolRAMCalendarPrefixPages

namespace OAI
/-! # All dated source widths from the single native execution -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleInput
open WireTelescope AdaptiveProbe ProtocolRAM ProtocolRAM.Calendar RoleProgram CatalystArchive PrefixReserve
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
variable {F : Type*} [Field F] {k edges : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (h width : ℕ)
    (r : ℕ) (route : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => Stages h (2^v.W)
local notation "W" => wordBits h (2^v.W) copies
local notation "C" => v.nativeChart P h width r route src tab dst owners
local notation "G" => v.privateArena P h width
local notation "bs" => v.stockBanks P h width
local notation "cells" => PurchaseInventory.footprint h N k
local notation "axes" => Fintype.card (Columns h (2^v.W))*k
local notation "oldRows" => Fintype.card (Old h v.W k edges)
local notation "stride" => v.keepLimit*width+1
local notation "slices" => sliceROM (P.joint.initial+cells) v.mesh.reserveSteps stride
local notation "es" => events v.mesh
local notation "axis" => CatalystArchive.pairKeys (Columns h (2^v.W)) k

private abbrev nativeInventoryAt (h d k edges base j : ℕ) (lw : PrefixWidths.Layout edges)
    (lr : PrefixWidths.Layout (Fintype.card (Columns h (2^d)) * k))
    (old : RouteSettlement.Banks) : Inventory :=
  let reserve := PrefixReserve.banks lr old j
  Inventory.ofOriginal base (Fintype.card (Old h d k edges))
    (lw.bank j) (lw.bank j) reserve.reserved reserve.used

variable (base : ℕ) (lw : PrefixWidths.Layout edges)
    (lr : PrefixWidths.Layout (Fintype.card (Columns h (2^v.W)) * k))
    (old : RouteSettlement.Banks) (j : ℕ)
local notation "banks" => PrefixReserve.banks lr old j
local notation "g" => nativeInventoryAt h v.W k edges base j lw lr old

def nativeAmount : Expr :=
  let inventory := nativeInventoryAt h v.W k edges base j lw lr old
  amount inventory (v.prefix_goods_expr P h width r route src tab dst owners j inventory.index)

def nativeId : Expr :=
  let inventory := nativeInventoryAt h v.W k edges base j lw lr old
  id inventory edges (PurchaseInventory.footprint h (Stages h (2^v.W)) k)

def currentFlow (init : Memory W) (i : Goods h v.W k) : ℕ :=
  let m:=StockBound.state C init j
  let ev:=es[j]?
  let a:=PurchaseInventory.stock (DatedGoods.previous v.mesh bs j) m i
  let s:=PurchaseInventory.stock (DatedGoods.stash bs ev) m i
  a+held v.mesh.inject width (DatedGoods.phase v.mesh ev)*payloadUnit i+
    (if DatedGoods.bought (C).modeAt ev m then held v.mesh.reserveSteps s (DatedGoods.releases ev) else 0)

/-- The only data about the paid and reserve banks are the two prefix readbacks
of `PrefixReserve.after_widths`. All commodity words are reconstructed using
the original feed and mode values at this date on that same final memory. -/
theorem amount_eval_at (init fixture M archive : Memory W) (compile : Event→List PaidWidths.Slice)
    (issued : Attempt→Entry axes width) (o : Fin oldRows)
    (hdr : RoleRoom.StockResident (h:=h) («W»:=v.W) (k:=k) (edges:=edges) base M)
    (wide : 2<2^W) (rowRoom : oldRows≤2^W) (edgeRoom : edges≤2^W) (axisRoom : axes≤2^W)
    (fuelRoom : fuel v.mesh*width<2^W) (hj : j≤(es).length)
    (origin : P.joint.initial+cells+(slices).size≤(G).first) (space : (G).endAddress v.mesh<2^W)
    (bounded : StockBound.Run C bs init h N k (v.keepLimit*width))
    (snapshot : ∀x<(G).endAddress v.mesh,M x=run C es init x)
    (installed : ∀x,(slices).base≤x→x<(slices).base+v.mesh.reserveSteps*stride→
      init x=feedAdvice slices v.mesh.reserveSteps stride fixture x)
    (payload : width≤2^h) (stockFit : v.keepLimit*width+1≤2^h)
    (paid : ∀e : Fin edges,(M ((lw.bank j).base+e.val)).val=PaidWidths.total (PrefixWidths.prefixRows es compile j) archive e)
    (reserves : ∀a : Fin axes,(M ((banks).used.base+a.val)).val=
      (∑i : Fin (recordCount v.mesh issued),if ((rank v.mesh issued).symm i).1.val<j ∧
        CatalystArchive.site v.mesh issued i=a then CatalystArchive.debit v.mesh issued i else 0) ∧
      (M ((banks).reserved.base+a.val)).val=fuel v.mesh*width) :
    ((nativeAmount v P h width r route src tab dst owners base lw lr old j).eval M (o.val:Word W)).val=
      Sum.elim (PaidWidths.total (PrefixWidths.prefixRows es compile j) archive)
        (Sum.elim (currentFlow v P h width r route src tab dst owners j init)
          (fun a=>fuel v.mesh*width-PrefixReserve.used (CatalystArchive.site v.mesh issued)
            (CatalystArchive.debit v.mesh issued) (countAt v.mesh issued j) (axis a)))
        (SettledMatrix.Layout.numbered o) := by
  apply amount_eval base M (lw.bank j) (lw.bank j) (banks).reserved (banks).used hdr wide rowRoom o
  · intro e
    have inBank : e.val < (lw.bank j).size := e.isLt.trans_le lw.covered
    rw [Bank.read, Fin.val_cast_of_lt (e.isLt.trans_le edgeRoom), Nat.mod_eq_of_lt inBank]
    exact paid e
  · intro i index
    exact v.prefix_goods_val P h width r route src tab dst owners init fixture M j hj (g).index (o.val:Word W) i
      origin space bounded snapshot installed payload stockFit index
  · intro a index
    exact PrefixReserve.leftExpr_val v.mesh issued lr old j M (g).index (o.val:Word W) (axis a)
      axisRoom fuelRoom index (reserves _)

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleInput
end

end OAI

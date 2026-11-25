import OAI.Hierarchy.ProbeFixedStockOperands
import OAI.Hierarchy.ProbeFixedBornSourceEnd
import OAI.Hierarchy.ProtocolRAMDiagnosticFits
import OAI.Hierarchy.ProtocolRAMCoreRouteSafe

namespace OAI
/-! # Physical endpoint and purchase-key reads on the fixed calendar -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard PurchaseFrozen
open StripChart StripDirectory BoughtSockets ReportSockets
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "d" => 2^v.W
local notation "W" => wordBits z d copies
local notation "G" => v.privateArena P z width
local notation "D" => P.routes.directory
local notation "B" => v.nativeBoards P z width
local notation "f" => v.nativeFormats P z width
local notation "geo" => v.located (v.seed P z width) P width
local notation "labelled" => withPorts geo v.mesh P.catalogue P.routes

theorem purchase_core_cover (K g h R : ℕ) (b : JointHeader.Board) (cat : CatalogueRows.Board)
    (orig : BoughtSockets.Directory ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))
    (allocated : CoreRoute.stop v.sampler z v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)
      v.depth K g h R ≤ b.initial) :
    let Q:=v.catalystPlacement z K g h R b cat orig
    ColumnROM.Cover z v.W Q.routes.directory.remapBase Q.routes.directory.sitesBase
      Q.routes.directory.superBase Q.routes.oldGroups Q.routes.bins Q.routes.height b.initial :=
  (CoreRoute.column_bounds v.sampler z v.W k _ v.depth K g h R b.initial allocated).2

private theorem outer_tiles_before_keys {h radix lanes letters depth : ℕ}
    [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages h radix)) lanes)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) lanes)]
    (s : StripChart.Boards h radix lanes letters depth) (phase trial stock : ℕ)
    (hd : 1≤radix) (i : Key h radix lanes) :
    let sh:=(s.outer phase trial).market.shelf
    let L:=sh.L s.sampler depth i
    L.source.base+L.source.size≤(build F s (.outer phase trial) stock).board.keys := by
  intro sh L
  let x:=build F s (.outer phase trial) stock
  let flags:=StripDirectory.flagBank sh s.sampler h radix lanes depth
  obtain ⟨_,_,_,_,_,source,gates,tape,last⟩:=L.regions
  have block : L.endAddress≤flags.base :=
    (sh.end_le s.sampler depth i hd).trans
      ((sh.final_after s.sampler depth i).trans (Nat.le_add_right ..))
  have sourceEnd : L.source.base+L.source.size≤L.endAddress := by omega
  have fl : flags.base=x.market.flags := rfl
  have tail : x.market.flags ≤ x.testsStart := Nat.le_add_right ..
  have mask : x.testsStart≤x.maskStart := by unfold Format.maskStart PostLayout.afterTests;omega
  have key : x.maskStart≤x.board.keys := Nat.le_add_right ..
  exact sourceEnd.trans (block.trans (fl.le.trans (tail.trans (mask.trans key))))

theorem purchase_outer_tiles (p a : ℕ) (i : Key z d k) :
    let sh:=((B).outer p a).market.shelf
    let L:=sh.L (B).sampler v.depth i
    L.source.base+L.source.size≤(f (.outer p a)).board.keys :=
  outer_tiles_before_keys (F:=F) B p a
    (resolvedStock v.mesh G P.joint.initial (build F B) (.outer p a)) Nat.one_le_two_pow i

theorem purchase_header_fits (a : Attempt)
    (room : (f a).board.keys<2^W)
    (columns : ColumnROM.Cover z v.W (D).remapBase (D).sitesBase (D).superBase
      P.routes.oldGroups P.routes.bins P.routes.height P.joint.initial)
    (keyRoom : (stratumHeader z d k v.sampler.degree v.depth (D).keysBase).stop≤P.joint.initial) :
    LinkOperands (f a).board.purchaseLink W (f a).board.keys ∧
      (f a).board.purchaseMenu.Fits W (f a).board.keys := by
  let cut:=(f a).board.keys
  let base:=(G).base v.mesh (.attempt a)
  have floor : base≤cut := (Nat.le_add_right ..).trans (v.stock_keys P z width a).1
  have smaller : P.joint.initial≤cut :=
    (v.catalyst_initial_le_first P z width).trans ((Nat.le_add_right ..).trans floor)
  have pages : ColumnROM.Cover z v.W (D).remapBase (D).sitesBase (D).superBase
      P.routes.oldGroups P.routes.bins P.routes.height cut :=
    ⟨columns.ct.trans smaller,columns.names.trans smaller,columns.super.trans smaller,
      columns.offsets.trans smaller,columns.sites.trans smaller⟩
  have keys := keyRoom.trans smaller
  cases a with
  | outer p a =>
    have links:=purchaseHeader_before labelled v.mesh P.catalogue P.routes p a pages
      (v.purchase_outer_tiles P z width p a) keys
    have lookup:=purchaseKey_before labelled p a keys
    exact ⟨⟨Expr.fits_of_inputEnd _ links.1 room,Expr.fits_of_inputEnd _ links.2.1 room,
      Expr.fits_of_inputEnd _ links.2.2.1 room,trivial⟩,Expr.fits_of_inputEnd _ lookup room⟩
  | inner p a j t =>
    have saved:= (v.catalyst_bought_bank_room P z width p a j t).2
    have links:=purchaseHeader_before labelled v.mesh P.catalogue P.routes p a pages
      (fun i=>(saved i).trans floor) keys
    have lookup:=purchaseKey_before labelled p a keys
    exact ⟨⟨Expr.fits_of_inputEnd _ links.1 room,Expr.fits_of_inputEnd _ links.2.1 room,
      Expr.fits_of_inputEnd _ links.2.2.1 room,trivial⟩,Expr.fits_of_inputEnd _ lookup room⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

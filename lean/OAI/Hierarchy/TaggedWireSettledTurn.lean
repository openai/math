import OAI.Hierarchy.TaggedWireRoleTurnBoard
import OAI.Hierarchy.TaggedWireLiveOriginal
import OAI.Hierarchy.TaggedWireTurnLive
import OAI.Hierarchy.TaggedWirePaidFits

namespace OAI
/-! # The signed turn board reads the original settled goods, catalyst and paid inventories -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
open AdaptiveProbe WireTelescope ReportSockets ProtocolRAM Calendar TaggedShorterSupergroups CatalystArchive
open ThreeFlat.RAM DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {w h W k H attempts depth M R edges payload : ℕ} (S : PurchaseSampler)
    (order : Fin R≃Edges S h (2^W) k) (dir : Directory (reserved h W (copies k attempts)) H)
local notation "z" => shape (R:=R) S dir edges
local notation "N" => Fintype.card (Old h W k edges)
local notation "K" => Fintype.card (Columns h (2^W))*k


variable (start out : ℕ) (core : CatalogueRows.CoreSource) (paid : Bool→Socket)
    (fixedData goodsBank : Bank) (b : RouteSettlement.Banks)
local notation "T" => turnBoard (R:=R) S dir (edges:=edges) start out core paid
local notation "I" => Inventory.ofOriginal ((z).stop start) N fixedData goodsBank b.reserved b.used

theorem turn_ready (paidFits : ∀s,(paid s).Fits w out) (coreFits : core.All (Expr.Fits w out))
    (prior : (z).ceiling start≤out) (room : (T).endAt+3*N<2^w) (inv : (I).width.Fits w out) :
    (T).Ready w ∧ ∀j,((T).rawFields I j).Fits w out := by
  have above : out≤(T).endAt :=
    (Nat.le_add_right out (4*(T).old)).trans (Nat.le_add_right _ (4*edges))
  have fits : (z).ceiling start<2^w:=by omega
  have orig:=original_fits z start h W k core paid paidFits coreFits rfl rfl prior fits
  refine ⟨⟨field_fits z _ orig prior fits false,field_fits z _ paidFits prior fits true,by omega⟩,?_⟩
  intro j
  fin_cases j
  · exact (socket_fits z _ (orig false) prior fits).1
  · exact (socket_fits z _ (orig true) prior fits).1
  · exact inv

def usedBy (c : Mesh) (issued : Attempt→Entry K payload) (i : Catalysts h W k) :=
  usedAt (CatalystArchive.site c issued) (debit c issued) (pairKeys (Columns h (2^W)) k i)

theorem settled_live_ready (π : Equiv.Perm (Fin (2^h))) (m : Memory w)
    (resident : (tables S order dir edges).Resident start m) (inventory : StockResident (h:=h) (W:=W) (k:=k) (edges:=edges) ((z).stop start) m)
    (roy : CoreCatalogue.Rows core order dir π M m) (perm : ∀j:Fin (2^h),m j.val=((π j).val:Word w))
    (sites : siteLast h (2^W) k+1≤2^w) (wide : 4≤2^w) (room : (T).endAt+3*N<2^w)
    (ready : (T).Ready w) (rawFits : ∀j,((T).rawFields I j).Fits w out)
    («public» : Fintype.card (Public S h W k attempts)≤2^w) (axis : (siteLast h (2^W) k+1)*(2*k)≤2^w) (rowsFit : 2^h≤2^w)
    (mesh : Mesh) (issued : Attempt→Entry K payload) (counters : ∀j : Fin K,
      RouteSettlement.actual b.used m j.val=usedAt (CatalystArchive.site mesh issued) (debit mesh issued) j ∧
      RouteSettlement.actual b.reserved m j.val=fuel mesh*payload)
    (width : Fin edges→ℕ) (enough : ∀e,(fixedData.read m (e.val:Word w)).val≤width e)
    (pos : ∀i,0<width i→Bool→PaidPorts S h W k attempts)
    (sockets : ∀i hi side,Resolved S ((z).chart start) (paid side) m (i.val:Word w) (.inl (pos i hi side))) :
    let fixed:=(fun e:Fin edges=>(fixedData.read m (e.val:Word w)).val)
    let stock:=(fun i:Goods h W k=>(goodsBank.read m ((PurchaseInventory.slot i:ℕ):Word w)).val)
    let total:=(fun _:Catalysts h W k=>fuel mesh*payload)
    let used:=usedBy mesh issued
    let old:=SettledMatrix.Layout.bits fixed stock total used
    let before:=fun (i : Fin N) (_:0<old i) side=>publicRoleFor S π (activePaid S width pos) (SettledMatrix.Layout.numbered i) side
    ((T).extended I w).Exec m ((T).extendedState I m) ((T).extendedTime I) ∧
      Board.LiveReads S T old width before (fun i hi s=>.inl (pos i hi s)) ((T).extendedState I m) := by
  intro fixed stock total used old before
  have oldRoom : N≤2^w:=by omega
  apply Board.extended_live S T I m ready rawFits room sites old width before (fun i hi s=>.inl (pos i hi s)) _ _ sockets
  · intro i
    let row : Fin N := ⟨i.val,i.isLt⟩
    refine (settled_width ((z).stop start) m fixedData goodsBank b inventory (by omega)
      oldRoom mesh issued counters row).trans ?_
    change _=SettledMatrix.Layout.available fixed stock total used (SettledMatrix.Layout.numbered row)
    cases SettledMatrix.Layout.numbered (r:=edges) («I»:=Goods h W k) (A:=Catalysts h W k) row <;> rename_i t
    · rfl
    · cases t <;> rfl
  · intro i hi side
    exact mixed_original S order dir π start m resident oldRoom core roy wide sites «public» rowsFit axis perm paid
      width fixed stock total used enough pos sockets i hi side

theorem settled_live (π : Equiv.Perm (Fin (2^h))) (m : Memory w)
    (resident : (tables S order dir edges).Resident start m) (inventory : StockResident (h:=h) (W:=W) (k:=k) (edges:=edges) ((z).stop start) m)
    (roy : CoreCatalogue.Rows core order dir π M m) (perm : ∀j:Fin (2^h),m j.val=((π j).val:Word w))
    (sites : siteLast h (2^W) k+1≤2^w) (wide : 4≤2^w) (room : (T).endAt+3*N<2^w)
    (prior : (z).ceiling start≤out) (paidFits : ∀s,(paid s).Fits w out) (coreFits : core.All (Expr.Fits w out))
    (inventoryFits : (I).width.Fits w out)
    («public» : Fintype.card (Public S h W k attempts)≤2^w) (axis : (siteLast h (2^W) k+1)*(2*k)≤2^w) (rowsFit : 2^h≤2^w)
    (mesh : Mesh) (issued : Attempt→Entry K payload) (counters : ∀j : Fin K,
      RouteSettlement.actual b.used m j.val=usedAt (CatalystArchive.site mesh issued) (debit mesh issued) j ∧
      RouteSettlement.actual b.reserved m j.val=fuel mesh*payload)
    (width : Fin edges→ℕ) (enough : ∀e,(fixedData.read m (e.val:Word w)).val≤width e)
    (pos : ∀i,0<width i→Bool→PaidPorts S h W k attempts)
    (sockets : ∀i hi side,Resolved S ((z).chart start) (paid side) m (i.val:Word w) (.inl (pos i hi side))) :
    let fixed:=(fun e:Fin edges=>(fixedData.read m (e.val:Word w)).val)
    let stock:=(fun i:Goods h W k=>(goodsBank.read m ((PurchaseInventory.slot i:ℕ):Word w)).val)
    let total:=(fun _:Catalysts h W k=>fuel mesh*payload)
    let used:=usedBy mesh issued
    let old:=SettledMatrix.Layout.bits fixed stock total used
    let before:=fun (i : Fin N) (_:0<old i) side=>publicRoleFor S π (activePaid S width pos) (SettledMatrix.Layout.numbered i) side
    ((T).extended I w).Exec m ((T).extendedState I m) ((T).extendedTime I) ∧
      Board.LiveReads S T old width before (fun i hi s=>.inl (pos i hi s)) ((T).extendedState I m) := by
  have ready := turn_ready (R:=R) S dir start out core paid fixedData goodsBank b
    paidFits coreFits prior room inventoryFits
  exact settled_live_ready S order dir start out core paid fixedData goodsBank b π m
    resident inventory roy perm sites wide room ready.1 ready.2 «public» axis rowsFit
    mesh issued counters width enough pos sockets

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom

end
end OAI

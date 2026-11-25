import OAI.Hierarchy.TaggedWireRoleRoomNative
import OAI.Hierarchy.TaggedWireOldBoardNative
import OAI.Hierarchy.ProbeCatalystArchiveGeometry
import OAI.Hierarchy.ProtocolRAMPurchaseInventory

namespace OAI
/-! # Native widths of the original paid, commodity and catalyst rows -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
open AdaptiveProbe ReportSockets ProtocolRAM TaggedShorterSupergroups WireTelescope
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {h W k attempts H R w edges : ℕ} (S : PurchaseSampler)
variable (order : Fin R≃Edges S h (2^W) k)
variable (dir : Directory (reserved h W (copies k attempts)) H)
local notation "N" => Fintype.card (Old h W k edges)

def stockWord (kind : Bool) (r : Fin N) :=
  Inventory.decode (edges:=edges) (PurchaseInventory.slot : Goods h W k→ℕ)
    (fun c : Catalysts h W k=>(CatalystArchive.pairKeys (Columns h (2^W)) k c).val) kind r

def stockPage (kind : Bool) : RoleROM.Page :=
  ⟨N,stockWord (edges:=edges) (h:=h) (W:=W) (k:=k) kind⟩

def mountStocks (edges start : ℕ) (raw : Memory w) :=
  let z := shape (R:=R) S dir edges
  mount S order dir edges start (RoleROM.publish (z.stop start)
    [stockPage (h:=h) (W:=W) (k:=k) (edges:=edges) true,
     stockPage (h:=h) (W:=W) (k:=k) (edges:=edges) false] raw)

/-- The row-kind and account-index pages use the free space already
covered by the original rounded-bank ceiling. -/
theorem stock_room (edges start : ℕ) :
    let z := shape (R:=R) S dir edges
    z.stop start+z.old+(RoleROM.bank (z.stop start+z.old) z.old).size≤z.ceiling start := by
  let z := shape (R:=R) S dir edges
  have «meta» : 7*z.old≤z.stop start := by
    unfold Sizes.stop Sizes.offset Sizes.positive Sizes.axis Sizes.ext Sizes.free Sizes.pub
    omega
  have span := ProtocolRAMPurchaseSampler.span_le z.old
  change z.stop start+z.old+ProtocolRAMPurchaseSampler.span z.old≤3*(z.stop start+1)
  omega

structure StockResident (base : ℕ) (m : Memory w) : Prop where
  tag : RoleROM.Mounted base (stockWord (edges:=edges) (h:=h) (W:=W) (k:=k) true) m
  index : RoleROM.Mounted (base+N) (stockWord (edges:=edges) (h:=h) (W:=W) (k:=k) false) m

theorem stocks_ready (edges start : ℕ) (raw : Memory w) :
    let z := shape (R:=R) S dir edges
    let m := mountStocks S order dir edges start raw
    (tables S order dir edges).Resident start m ∧ SiteROM.Resident dir (z.offset start) m ∧
      StockResident (h:=h) (W:=W) (k:=k) (edges:=edges) (z.stop start) m := by
  let z := shape (R:=R) S dir edges
  let tag := stockPage (h:=h) (W:=W) (k:=k) (edges:=edges) true
  let key := stockPage (h:=h) (W:=W) (k:=k) (edges:=edges) false
  let inner := RoleROM.publish (z.stop start) [tag,key] raw
  obtain ⟨body,sites⟩ := ready S order dir edges start inner
  refine ⟨body,sites,?_⟩
  have tagRead := RoleROM.mounted_at [] tag [key] (z.stop start) raw
  have keyRead := RoleROM.mounted_at [tag] key [] (z.stop start) raw
  constructor
  · intro i
    rw [show mountStocks S order dir edges start raw (z.stop start+i.val)=inner (z.stop start+i.val) from
      outside S order dir edges start _ inner (Or.inr (Nat.le_add_right (z.stop start) i.val))]
    exact tagRead i
  · intro i
    change mountStocks S order dir edges start raw (z.stop start+z.old+i.val) =
      (key.word i : Word w)
    refine (outside S order dir edges start _ inner (Or.inr
      ((Nat.le_add_right (z.stop start) z.old).trans (Nat.le_add_right _ i.val)))).trans ?_
    have rows : tag.rows = z.old := rfl
    simpa only [RoleROM.words,Nat.add_zero,rows,inner,List.cons_append,List.nil_append] using keyRead i

theorem StockResident.frame {base : ℕ} {m last : Memory w}
    (s : StockResident (h:=h) (W:=W) (k:=k) (edges:=edges) base m)
    (keep : ∀u,base≤u → u<base+2*N → last u=m u) :
    StockResident (h:=h) (W:=W) (k:=k) (edges:=edges) base last := by
  constructor
  · intro i
    have hi := i.isLt
    rw [keep _ (by omega) (by omega)]
    exact s.tag i
  · intro i
    have hi := i.isLt
    rw [keep _ (by omega) (by omega)]
    exact s.index i

/-- The native driver can append this advice after its working area.
Preserving that one interval through the run preserves every literal
geometry, role and inventory lookup in the terminal evaluator. -/
theorem retained (edges start : ℕ) (raw final : Memory w)
    (keep : ∀u,start≤u → u < (shape (R:=R) S dir edges).ceiling start →
      final u=mountStocks S order dir edges start raw u) :
    let z := shape (R:=R) S dir edges
    (tables S order dir edges).Resident start final ∧ SiteROM.Resident dir (z.offset start) final ∧
      StockResident (h:=h) (W:=W) (k:=k) (edges:=edges) (z.stop start) final := by
  let z := shape (R:=R) S dir edges
  have left : start≤z.offset start := by
    unfold Sizes.offset Sizes.positive Sizes.axis Sizes.ext Sizes.free Sizes.pub
    omega
  have stop : z.offset start≤z.stop start := Nat.le_add_right ..
  have size : z.stop start+2*z.old≤z.ceiling start := by
    have span : z.old≤ProtocolRAMPurchaseSampler.span z.old := (ProtocolRAMPurchaseSampler.lt_span _).le
    have bank := stock_room (R:=R) S dir edges start
    change z.stop start+z.old+ProtocolRAMPurchaseSampler.span z.old≤z.ceiling start at bank
    omega
  obtain ⟨roles,geometry,stock⟩ := stocks_ready S order dir edges start raw
  have upper : z.stop start ≤ z.ceiling start :=
    (Nat.le_add_right _ _).trans size
  refine ⟨Tables.Resident.frame _ roles (fun u lo hi=>keep u lo ((hi.trans_le stop).trans_le upper)),?_,?_⟩
  · apply geometry.frame
    intro u lo hi
    change z.offset start ≤ u at lo
    change u < z.stop start at hi
    exact keep u (left.trans lo) (hi.trans_le upper)
  · apply stock.frame
    intro u lo hi
    change z.stop start ≤ u at lo
    change u < z.stop start + 2*z.old at hi
    exact keep u ((left.trans stop).trans lo) (hi.trans_le size)

set_option maxHeartbeats 900000 in
/-- The physical decoder reads the two kinds of original stock arrays
and the settled reserve difference at their genuine numerical keys. -/
theorem stock_width (base : ℕ) (m : Memory w) (paid active reserved used : Bank)
    (read : StockResident (h:=h) (W:=W) (k:=k) (edges:=edges) base m)
    (wide : 2<2^w) (room : N≤2^w)
    (fund : ∀c : Catalysts h W k,
      let j : Word w := (CatalystArchive.pairKeys (Columns h (2^W)) k c).val
      (used.read m j).val≤(reserved.read m j).val) (r : Fin N) :
    ((Inventory.ofOriginal base N paid active reserved used).width.eval m (r.val:Word w)).val =
      match SettledMatrix.Layout.numbered (r:=edges) (I:=Goods h W k) (A:=Catalysts h W k) r with
      | .inl p => (paid.read m (p.val:Word w)).val
      | .inr (.inl i) => (active.read m ((PurchaseInventory.slot i:ℕ):Word w)).val
      | .inr (.inr c) =>
        let j : Word w := (CatalystArchive.pairKeys (Columns h (2^W)) k c).val
        (reserved.read m j).val-(used.read m j).val := by
  let chart := Inventory.ofOriginal base N paid active reserved used
  have reads := Inventory.original_read (edges:=edges)
    (PurchaseInventory.slot : Goods h W k→ℕ)
    (fun c : Catalysts h W k=>(CatalystArchive.pairKeys (Columns h (2^W)) k c).val)
    m base paid active reserved used N rfl read.tag read.index room r
  obtain ⟨tag,idx⟩ := reads
  have one : (1:Word w)≠0 := by
    intro eq
    have bad := congrArg Fin.val eq
    change 1%(2^w)=0 at bad
    rw [Nat.mod_eq_of_lt (by omega : 1<2^w)] at bad
    omega
  change (chart.width.eval m (r.val : Word w)).val = _
  rcases item : SettledMatrix.Layout.numbered (r:=edges) (I:=Goods h W k) (A:=Catalysts h W k) r with p|i|c
  · simp only [Inventory.decode,item] at tag idx
    exact congrArg Fin.val (Inventory.width_paid chart m (r.val : Word w) (p.val : Word w) tag idx)
  · simp only [Inventory.decode,item] at tag idx
    exact congrArg Fin.val (Inventory.width_goods chart m (r.val : Word w)
      ((PurchaseInventory.slot i : ℕ) : Word w) one tag idx)
  · simp only [Inventory.decode,item] at tag idx
    have nezero : chart.kind.eval m (r.val:Word w)≠0 := by
      intro eq
      have bad := congrArg Fin.val (tag.symm.trans eq)
      change ((2:ℕ)%(2^w))=0 at bad
      rw [Nat.mod_eq_of_lt wide] at bad
      omega
    have neone : chart.kind.eval m (r.val:Word w)≠1 := by
      intro eq
      have bad := congrArg Fin.val (tag.symm.trans eq)
      change ((2:ℕ)%(2^w))=1%(2^w) at bad
      rw [Nat.mod_eq_of_lt wide,Nat.mod_eq_of_lt (by omega : 1<2^w)] at bad
      omega
    exact Inventory.width_catalyst chart m _ _ nezero neone idx (fund c)

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
end

end OAI

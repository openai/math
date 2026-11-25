import OAI.Hierarchy.TaggedWireRoleInventory
import OAI.Hierarchy.TaggedWideDatedRows
import OAI.Hierarchy.TaggedWideReserveCell

namespace OAI
/-! # Dated stock amounts and sparse identifiers on physical original-row ordinals -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleInput
open ProtocolRAM ProtocolRAM.Calendar WireTelescope RoleProgram
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
variable {h W k edges w : ℕ}
local notation "Good" => Goods h W k
local notation "Axis" => Catalysts h W k
local notation "rows" => Fintype.card (Old h W k edges)
local notation "num" => PurchaseInventory.footprint h (Stages h (2^W)) k
local notation "axes" => Fintype.card (Columns h (2^W))*k
local notation "rank" => SettledMatrix.Layout.numbered (r:=edges) (I:=Good) (A:=Axis)
local notation "axis" => CatalystArchive.pairKeys (Columns h (2^W)) k

def amount (g : Inventory) (datedGoods : Expr) : Expr :=
  .branch .eq g.kind (.lit 0) (.lookup g.paid g.index)
    (.branch .eq g.kind (.lit 1) datedGoods (.op .sub (.lookup g.reserved g.index) (.lookup g.used g.index)))

def id (g : Inventory) (edges goods : ℕ) : Expr :=
  .branch .eq g.kind (.lit 0) g.index
    (.branch .eq g.kind (.lit 1) (.op .add (.lit edges) g.index) (.op .add (.lit (edges+goods)) g.index))

/-- The sparse order uses the original settlement's paid slot, followed by the
lane-major commodity ordinal and the original pair of catalyst axis indices. -/
def number : Old h W k edges→ℕ
  | .inl e=>e.val
  | .inr (.inl i)=>edges+PurchaseInventory.slot i
  | .inr (.inr a)=>edges+num+(axis a).val

def tag : Old h W k edges→ℕ
  | .inl _=>0 | .inr (.inl _)=>1 | .inr (.inr _)=>2

def localIndex : Old h W k edges→ℕ
  | .inl e=>e.val
  | .inr (.inl i)=>PurchaseInventory.slot i
  | .inr (.inr a)=>(axis a).val

theorem codes (wide : 2<2^w) : (1:Word w)≠0 ∧ (2:Word w)≠0 ∧ (2:Word w)≠1 := by
  have injective (a b : ℕ) (ha : a<2^w) (hb : b<2^w) (ne : a≠b) : (a:Word w)≠(b:Word w):=by
    intro same
    have eq:=congrArg Fin.val same
    exact ne (by simpa only [Fin.val_cast_of_lt ha,Fin.val_cast_of_lt hb] using eq)
  exact ⟨injective 1 0 (by omega) (by omega) (by decide),injective 2 0 wide (by omega) (by decide),
    injective 2 1 wide (by omega) (by decide)⟩

section
variable (base : ℕ) (m : Memory w) (paid active reserved used : Bank)
local notation "g" => Inventory.ofOriginal base rows paid active reserved used
variable (loaded : RoleRoom.StockResident (h:=h) (W:=W) (k:=k) (edges:=edges) base m)
    (wide : 2<2^w) (rowRoom : Fintype.card (Old h W k edges) ≤ 2^w)
    (r : Fin (Fintype.card (Old h W k edges)))
local notation "rr" => (r.val:Word w)

include loaded rowRoom in
theorem decoded :
    (g).kind.eval m rr=(tag (rank r):Word w) ∧ (g).index.eval m rr=(localIndex (rank r):Word w) := by
  have got:=Inventory.original_read (edges:=edges) (PurchaseInventory.slot : Good→ℕ)
    (fun a : Axis=>(axis a).val) m base paid active reserved used rows rfl loaded.tag loaded.index rowRoom r
  dsimp only at got
  rcases item : rank r with e|i|a <;>
    simpa only [Inventory.decode, item, tag, localIndex, Bool.false_eq_true, ite_false, ite_true] using got

include loaded wide rowRoom in
theorem id_eval :
    (id g edges num).eval m rr=(number (rank r):Word w) := by
  have lookup:=decoded base m paid active reserved used loaded rowRoom r
  have ne:=codes wide
  rcases kind : rank r with e|i|a <;>
    simp only [kind,tag,localIndex] at lookup <;>
    simp only [id, Expr.eval, Comparison.test, RowOp.opcode, BinaryOp.eval,
      lookup.1, lookup.2, number, Nat.cast_add, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
      beq_iff_eq, ite_true, ite_eq_right ne.1, ite_eq_right ne.2.1, ite_eq_right ne.2.2]

include loaded wide rowRoom in
theorem id_val (width : edges+(num+axes)≤2^w) : ((id g edges num).eval m rr).val=number (rank r) := by
  rw [id_eval base m paid active reserved used loaded wide rowRoom r]
  apply Fin.val_cast_of_lt
  rcases rank r with e|i|a
  · have small:=e.isLt
    change e.val<_
    omega
  · have small:=PurchaseInventory.slot_lt i
    change edges+PurchaseInventory.slot i<_
    omega
  · have small:=(axis a).isLt
    change edges+num+(axis a).val<_
    omega

include loaded wide rowRoom in
/-- Dispatch on the two original initialized source tables. The consumer may
supply the branch read only after its decoded physical ordinal is known. -/
theorem amount_eval (datedGoods : Expr) (paidBits : Fin edges→ℕ) (flow : Good→ℕ) (left : Axis→ℕ)
    (paidRead : ∀e : Fin edges,(paid.read m (e.val:Word w)).val=paidBits e)
    (goodRead : ∀i : Good,(g).index.eval m rr=(PurchaseInventory.slot i:Word w) →
        (datedGoods.eval m rr).val=flow i)
    (reserveRead : ∀a : Axis,(g).index.eval m rr=((axis a).val:Word w) →
      ((reserved.read m ((g).index.eval m rr))-(used.read m ((g).index.eval m rr))).val=left a) :
    ((amount g datedGoods).eval m rr).val=Sum.elim paidBits (Sum.elim flow left) (rank r) := by
  have lookup:=decoded base m paid active reserved used loaded rowRoom r
  have ne:=codes wide
  rcases kind : rank r with e|i|a
  · simp only [kind,tag,localIndex] at lookup
    simpa only [amount, Expr.eval, Comparison.test, lookup.1, lookup.2,
      Nat.cast_zero, beq_iff_eq, ite_true, Sum.elim_inl, show (g).paid = paid from rfl] using paidRead e
  · simp only [kind,tag,localIndex] at lookup
    simpa only [amount, Expr.eval, Comparison.test, lookup.1, Nat.cast_zero, Nat.cast_one,
      beq_iff_eq, ite_eq_right ne.1, ite_true, Sum.elim_inr, Sum.elim_inl] using goodRead i lookup.2
  · simp only [kind,tag,localIndex] at lookup
    simpa only [amount, Expr.eval, Comparison.test, RowOp.opcode, BinaryOp.eval, lookup.1,
      Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, beq_iff_eq, ite_eq_right ne.2.1,
      ite_eq_right ne.2.2, Sum.elim_inr, show (g).reserved = reserved from rfl,
      show (g).used = used from rfl] using reserveRead a lookup.2

end

theorem amount_fits (g : Inventory) (goods : Expr) (dest : ℕ) (kind : g.kind.Fits w dest)
    (index : g.index.Fits w dest) (paid : g.paid.Fits w dest) (stock : goods.Fits w dest)
    (reserved : g.reserved.Fits w dest) (used : g.used.Fits w dest) : (amount g goods).Fits w dest :=
  ⟨kind,True.intro,⟨paid,index⟩,kind,True.intro,stock,⟨reserved,index⟩,used,index⟩

theorem id_fits (g : Inventory) (edges goods dest : ℕ) (kind : g.kind.Fits w dest) (index : g.index.Fits w dest) :
    (id g edges goods).Fits w dest :=
  ⟨kind,True.intro,index,kind,True.intro,⟨True.intro,index⟩,True.intro,index⟩

theorem amount_work (g : Inventory) (goods : Expr) :
    (amount g goods).work=2*g.kind.work+3*g.index.work+goods.work+20 := by simp [amount,Expr.work];omega

theorem id_work (g : Inventory) (edges goods : ℕ) : (id g edges goods).work=2*g.kind.work+3*g.index.work+8 := by
  simp [id,Expr.work]
  omega

section NativeOrder
open ProtocolRAM.Calendar.CatalogueRows AdaptiveProbe
variable {attempts n : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : ReportSockets.Marks h W k attempts) (b : CatalogueRows.Board) (order : Fin b.coreRows≃Edges S h (2^W) k)
    (size : attempts*(ProtocolRAM.PurchaseFrozen.count h (2^W) k*ProtocolRAM.PurchaseFrozen.paths h S.degree depth)=b.boughtRows)
    (orderRows : Fin n≃Source S π depth marked)
local notation "raw" => DatedRows.raw S π depth marked b order size orderRows
local notation "ord" => b.ordinal S π depth marked order size
local notation "sparse" => sparseKey S π depth marked b order size (PurchaseInventory.slotEquiv h (Stages h (2^W)) k) axis

theorem number_at (i : Fin n) : number (SettledMatrix.Layout.numbered (raw i))=(sparse (orderRows i)).val := by
  rw [DatedRows.numbered_raw]
  cases row : orderRows i with
  | inl paid=>exact (key_paid ..).symm
  | inr stock=>
    cases stock with
    | inl good=>
      change b.rows + PurchaseInventory.slot good = _
      simpa only [PurchaseInventory.slotEquiv_val] using
        (key_goods S π depth marked b order size (PurchaseInventory.slotEquiv h (Stages h (2^W)) k) axis good).symm
    | inr active=>exact (key_reserve ..).symm

theorem width_at (paid : Fin b.rows→ℕ) (flow : Good→ℕ) (left : Axis→ℕ) (i : Fin n) :
    Sum.elim paid (Sum.elim flow left) (SettledMatrix.Layout.numbered (raw i))=
      Sum.elim (fun e=>paid (ord e)) (Sum.elim flow left) (orderRows i) := by
  rw [DatedRows.numbered_raw]
  rcases orderRows i with e|a|c <;> rfl

theorem width_blank (paid : Fin b.rows→ℕ) (flow : Good→ℕ) (left : Axis→ℕ)
    (support : ∀e : Fin b.rows,0<paid e→e∈Set.range ord)
    (r : Fin (Fintype.card (Old h W k b.rows)))
    (blank : DatedRows.lookup S π depth marked b order size orderRows r=none) :
    Sum.elim paid (Sum.elim flow left) (SettledMatrix.Layout.numbered r)=0 := by
  obtain ⟨e,eqn,absent⟩:=DatedRows.lookup_dormant S π depth marked b order size orderRows blank
  rw [eqn]
  exact Nat.eq_zero_of_not_pos (fun h=>absent (support e h))

end NativeOrder

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleInput
end

end OAI

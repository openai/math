import OAI.Hierarchy.TaggedWireGoodsCursor
import OAI.Hierarchy.TaggedWideGoodsWidth
import OAI.Hierarchy.ProtocolRAMCalendarHeldStock
import OAI.Hierarchy.ProbeCommodityBounds

namespace OAI
/-! # Concrete commodity-width operand on the permanent original RAM archive -/
namespace Hierarchy.ProtocolRAM.Calendar.DatedGoods
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing
noncomputable section
variable {z N k W : ℕ}
local notation "Good" => Commodity (Fin (2^z)) N k

def parentMode (modeAt : Attempt→ℕ) (e : Option Event) : Expr :=
  (parent e).elim (.lit 0) (fun a=>word (modeAt a))

def bank (base z N k : ℕ) : Bank := ⟨base,ProtocolRAMPurchaseSampler.bits (PurchaseInventory.footprint z N k)⟩

def payloadRow (z : ℕ) (ix : Expr) : Expr := .branch .lt ix (.lit (2^z)) (.lit 1) (.lit 0)

def term (z N k : ℕ) (c : Mesh) (b : StockBound.Banks) (modeAt : Attempt→ℕ)
    (slices : Bank) (stride payload j : ℕ) (e : Option Event) (ix : Expr) : Expr :=
  goodsWidth slices stride c payload (phase c e) (releases e) (.lookup (bank (previous c b j) z N k) ix)
    (.lookup (bank (stash b e) z N k) ix) (payloadRow z ix) (parentMode modeAt e)

theorem payload_index (i : Good) : (PurchaseInventory.slot i<2^z) ↔ payloadUnit i=1 := by
  cases i with
  | inl v=>simp [PurchaseInventory.slot,PurchaseInventory.lane,PurchaseInventory.record,payloadUnit]
  | inr term=>
    rcases term with ⟨⟨v,t⟩,a⟩
    simp only [PurchaseInventory.slot,PurchaseInventory.lane,PurchaseInventory.record,payloadUnit,Nat.zero_ne_one,iff_false]
    apply not_lt.mpr
    exact (Nat.le_mul_of_pos_left _ (by omega)).trans (Nat.le_add_right ..)

theorem payload_read (ix : Expr) (m : Memory W) (r : Word W) (i : Good)
    (room : PurchaseInventory.footprint z N k≤2^W) (small : 2^z<2^W)
    (index : ix.eval m r=(PurchaseInventory.slot i:Word W)) :
    (payloadRow z ix).eval m r=0 ↔ decide (payloadUnit i=1)=false := by
  have compare : ((PurchaseInventory.slot i:Word W)<(2^z:ℕ)) ↔ payloadUnit i=1 := by
    change (PurchaseInventory.slot i:Word W).val < ((2^z:ℕ):Word W).val ↔ _
    rw [Fin.val_cast_of_lt ((PurchaseInventory.slot_lt i).trans_le room),Fin.val_cast_of_lt small]
    exact payload_index i
  have one : (1:Word W)≠0 := by
    intro h
    have vals:=congrArg Fin.val h
    change ((1:ℕ):Word W).val=0 at vals
    rw [Fin.val_cast_of_lt (Nat.one_le_two_pow.trans_lt small)] at vals
    omega
  simp only [payloadRow, Expr.eval, Comparison.test, index, decide_eq_true_eq, compare,
    Nat.cast_one, Nat.cast_zero]
  by_cases isPayload : payloadUnit i = 1 <;> simp [isPayload, one]

theorem bank_read (base : ℕ) (m : Memory W) (i : Good) (room : PurchaseInventory.footprint z N k≤2^W) :
    (bank base z N k).read m (PurchaseInventory.slot i:Word W)=m (base+PurchaseInventory.slot i) := by
  rw [Bank.read, Fin.val_cast_of_lt ((PurchaseInventory.slot_lt i).trans_le room)]
  change m (base + PurchaseInventory.slot i % ProtocolRAMPurchaseSampler.span (PurchaseInventory.footprint z N k)) = _
  rw [Nat.mod_eq_of_lt ((PurchaseInventory.slot_lt i).trans (ProtocolRAMPurchaseSampler.lt_span _))]

theorem mode_read (m : Memory W) (modeAt : Attempt→ℕ) (e : Option Event) (r : Word W)
    (wide : 3<2^W) : (parentMode modeAt e).eval m r=(3:Word W) ↔ bought modeAt e m=true := by
  cases h : parent e with
  | none=>
    have ne : (0:Word W)≠3 := by
      intro eq
      have vals:=congrArg Fin.val eq
      change 0=((3:ℕ):Word W).val at vals
      rw [Fin.val_cast_of_lt wide] at vals
      omega
    simp [parentMode,bought,h,Expr.eval,ne]
  | some a=>simp [parentMode,bought,h,word_eval]

/-- This reads the two persisted source banks and enters the slice ROM exactly
once for each original preceding inner feed. -/
theorem read (c : Mesh) (b : StockBound.Banks) (modeAt : Attempt→ℕ)
    (slices : Bank) (stride payload j : ℕ) (e : Option Event) (ix : Expr)
    (out entry : Memory W) (r : Word W) (i : Good)
    (room : PurchaseInventory.footprint z N k≤2^W) (small : 2^z<2^W) (wide : 3<2^W)
    (index : ix.eval out r=(PurchaseInventory.slot i:Word W))
    (active : out (previous c b j+PurchaseInventory.slot i)=entry (previous c b j+PurchaseInventory.slot i))
    (saved : out (stash b e+PurchaseInventory.slot i)=entry (stash b e+PurchaseInventory.slot i))
    (mode : bought modeAt e out=bought modeAt e entry)
    (rom : ∀s<c.reserveSteps,slices.read out ((s*stride+PurchaseInventory.stock (stash b e) entry i:ℕ):Word W)=
      (slice c.reserveSteps (PurchaseInventory.stock (stash b e) entry i) s:Word W)) :
    (term z N k c b modeAt slices stride payload j e ix).eval out r=
      ((PurchaseInventory.stock (previous c b j) entry i+held c.inject payload (phase c e)*payloadUnit i+
        (if bought modeAt e entry then held c.reserveSteps (PurchaseInventory.stock (stash b e) entry i) (releases e) else 0):ℕ):Word W) := by
  have get (base : ℕ) (frame : out (base+PurchaseInventory.slot i)=entry (base+PurchaseInventory.slot i)) :
      (Expr.lookup (bank base z N k) ix).eval out r=(PurchaseInventory.stock base entry i:Word W) := by
    simp only [Expr.eval,index,bank_read _ _ _ room,PurchaseInventory.stock,Fin.cast_val_eq_self,frame]
  have payloadBit : (decide (payloadUnit i=1)).toNat=payloadUnit i := by cases i <;> rfl
  simpa only [term, payloadBit] using goodsWidth_read slices stride c payload (phase c e) (releases e) _ _ _ _ out r
    (PurchaseInventory.stock (previous c b j) entry i) (PurchaseInventory.stock (stash b e) entry i)
    (decide (payloadUnit i=1)) (bought modeAt e entry) (get _ active) (get _ saved)
    (payload_read ix out r i room small index) ((mode_read out modeAt e r wide).trans (by rw [mode])) rom

theorem held_fits (s : Bank) (stride steps j : ℕ) (saved : Expr) (out : ℕ)
    (sf : saved.Fits W out) (table : s.Fits W out) : (heldExpr s stride steps saved j).Fits W out := by
  induction j with
  | zero=>exact sf
  | succ j ih=>
    rw [heldExpr]
    split
    · exact ⟨ih,table,True.intro,sf⟩
    · exact ih

theorem term_fits (z N k : ℕ) (c : Mesh) (b : StockBound.Banks) (modeAt : Attempt→ℕ)
    (slices : Bank) (stride payload j : ℕ) (e : Option Event) (ix : Expr) (out : ℕ)
    (idx : ix.Fits W out) (active : (bank (previous c b j) z N k).Fits W out)
    (saved : (bank (stash b e) z N k).Fits W out) (rom : slices.Fits W out)
    (mode : ∀a,parent e=some a→modeAt a+1≤out) (wide : 1<2^W) :
    (term z N k c b modeAt slices stride payload j e ix).Fits W out := by
  have bound : (parentMode modeAt e).Fits W out := by
    cases h : parent e with
    | none=>simp [parentMode,h,Expr.Fits]
    | some a=>
      simp only [parentMode,h,Option.elim_some]
      exact ⟨⟨by change (0 : ℕ) < 1; decide, wide, mode a h⟩, True.intro⟩
  have select : (payloadRow z ix).Fits W out:=⟨idx,True.intro,True.intro,True.intro⟩
  exact ⟨⟨⟨active,idx⟩,select,True.intro,True.intro,True.intro⟩,
    bound,True.intro,held_fits _ _ _ _ _ _ ⟨saved,idx⟩ rom,True.intro⟩

theorem held_work (s : Bank) (stride steps j : ℕ) (saved : Expr) :
    (heldExpr s stride steps saved j).work≤ saved.work+j*(saved.work+8) := by
  induction j with
  | zero=>simp [heldExpr]
  | succ j ih=>
    simp only [heldExpr,Nat.succ_mul]
    split
    · simp only [Expr.work]
      omega
    · omega

theorem held_work_limit (s : Bank) (stride steps j : ℕ) (saved : Expr) :
    (heldExpr s stride steps saved j).work≤ saved.work+min j steps*(saved.work+8) := by
  induction j with
  | zero=>simp [heldExpr]
  | succ j ih=>
    by_cases active : j<steps
    · rw [min_eq_left (Nat.succ_le_of_lt active),Nat.succ_mul,heldExpr,ite_eq_left active]
      rw [min_eq_left active.le] at ih
      simp only [Expr.work]
      omega
    · have full:=Nat.le_of_not_lt active
      rw [min_eq_right full] at ih
      rwa [min_eq_right (full.trans (Nat.le_succ _)),heldExpr,ite_eq_right active]

theorem term_work (z N k : ℕ) (c : Mesh) (b : StockBound.Banks) (modeAt : Attempt→ℕ)
    (slices : Bank) (stride payload j : ℕ) (e : Option Event) (ix : Expr) :
    (term z N k c b modeAt slices stride payload j e ix).work≤
      3*ix.work+29+releases e*(ix.work+13) := by
  have mode : (parentMode modeAt e).work≤6 := by
    cases h : parent e with
    | none=>simp [parentMode,h,Expr.work]
    | some a=>simp [parentMode,h,word,Expr.work]
  have work:=held_work slices stride c.reserveSteps (releases e) (.lookup (bank (stash b e) z N k) ix)
  simp only [Expr.work] at work
  rw [show ix.work+5+8 = ix.work+13 by omega] at work
  simp only [term,goodsWidth,Expr.work,payloadRow]
  omega

theorem term_work_limit (z N k : ℕ) (c : Mesh) (b : StockBound.Banks) (modeAt : Attempt→ℕ)
    (slices : Bank) (stride payload j : ℕ) (e : Option Event) (ix : Expr) :
    (term z N k c b modeAt slices stride payload j e ix).work≤
      3*ix.work+29+c.reserveSteps*(ix.work+13) := by
  have mode : (parentMode modeAt e).work≤6 := by
    cases h : parent e with
    | none=>simp [parentMode,h,Expr.work]
    | some a=>simp [parentMode,h,word,Expr.work]
  have bound:=held_work_limit slices stride c.reserveSteps (releases e) (.lookup (bank (stash b e) z N k) ix)
  simp only [Expr.work] at bound
  rw [show ix.work+5+8 = ix.work+13 by omega] at bound
  have use:=Nat.mul_le_mul_right (ix.work+13) (min_le_right (releases e) c.reserveSteps)
  simp only [term,goodsWidth,Expr.work,payloadRow]
  omega

end
end Hierarchy.ProtocolRAM.Calendar.DatedGoods

end OAI

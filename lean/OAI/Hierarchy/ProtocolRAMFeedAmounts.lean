import OAI.Hierarchy.ProtocolRAMCalendar
import OAI.Hierarchy.ProtocolRAMFeed

namespace OAI
/-! # The unclipped integer amount in each chronological commodity feed -/

namespace Hierarchy.ProtocolRAM.Calendar.CommodityColumn
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing

variable {w : ℕ}

def outerAmount (f : CommodityColumn) (c : Mesh) (p : ℕ) :=
  if p<c.inject then AdaptiveProbe.slice c.inject f.payload p else 0

def innerAmount (f : CommodityColumn) (c : Mesh) (p a j : ℕ) (addr : Attempt → ℕ)
    (m : Memory w) (r : Word w) :=
  if m (addr (.outer p a))=3 then AdaptiveProbe.slice c.reserveSteps (f.reserve.eval m r).val j else 0

private theorem add_value (v : Word w) (n : ℕ) (small : v.val+n<2^w) :
    (v+(n:Word w)).val=v.val+n := by
  rw [Fin.val_add,Fin.val_cast_of_lt (by omega : n<2^w),Nat.mod_eq_of_lt small]

theorem outer_total (f : CommodityColumn) (c : Mesh) (p : ℕ) (addr : Attempt → ℕ)
    (m : Memory w) (r : Word w) (room : (f.stock.eval m r).val+f.outerAmount c p<2^w) :
    ((total addr (.outer p) (f.feed c (.outer p))).eval m r).val=
      (f.stock.eval m r).val+f.outerAmount c p :=
  add_value _ _ room

/-- The nonrecord lanes receive zero injection even at a live outer boundary. -/
theorem outer_paid (f : CommodityColumn) (c : Mesh) (p width : ℕ) (paid : Bool)
    (payload : f.payload=if paid then width else 0) :
    f.outerAmount c p=(if paid ∧ p<c.inject then AdaptiveProbe.slice c.inject width p else 0) := by
  cases paid <;> by_cases inlet : p<c.inject <;>
    simp [outerAmount,inlet,payload,AdaptiveProbe.slice,AdaptiveProbe.delivered]

/-- A live read on the mutable tape agrees with the original mounted reserve-slice ROM.
Only locations occupied by the public table need to be preserved. -/
theorem slice_entry (bank : Bank) (steps stride : ℕ) (i : Fin steps) (b : Fin stride)
    (fixture m : Memory w) (size : steps*stride≤bank.size) (limit : steps*stride<2^w)
    (mounted : ∀ a, bank.base≤a → a<bank.base+steps*stride → m a=feedAdvice bank steps stride fixture a) :
    bank.read m ((i.val*stride+b.val : ℕ):Word w)=(AdaptiveProbe.slice steps b.val i.val : Word w) := by
  have block := Nat.mul_le_mul_right stride i.isLt
  rw [Nat.succ_mul] at block
  have digit := b.isLt
  have inside : i.val*stride+b.val<steps*stride := by omega
  calc
    _ = bank.read (feedAdvice bank steps stride fixture) ((i.val*stride+b.val : ℕ):Word w) := by
      simp only [Bank.read,Fin.val_cast_of_lt (inside.trans limit),Nat.mod_eq_of_lt (inside.trans_le size)]
      exact mounted _ (Nat.le_add_right ..) (by omega)
    _ = _ := feed_table bank steps stride i b fixture size limit

/-- The inner increment is enabled by the archived outer mode 3. It is zero on
every other archived mode, including an attempted purchase that did not buy. -/
theorem inner_total (f : CommodityColumn) (c : Mesh) (p a j : ℕ) (addr : Attempt → ℕ)
    (m : Memory w) (r : Word w) (fixture : Memory w)
    (index : j<c.reserveSteps) (digit : (f.reserve.eval m r).val<f.stride)
    (size : c.reserveSteps*f.stride≤f.feedTable.size) (limit : c.reserveSteps*f.stride<2^w)
    (mounted : ∀ x,f.feedTable.base≤x → x<f.feedTable.base+c.reserveSteps*f.stride →
      m x=feedAdvice f.feedTable c.reserveSteps f.stride fixture x)
    (room : (f.stock.eval m r).val+f.innerAmount c p a j addr m r<2^w) :
    ((total addr (.inner p a j) (f.feed c (.inner p a j))).eval m r).val=
      (f.stock.eval m r).val+f.innerAmount c p a j addr m r := by
  have entry := slice_entry f.feedTable c.reserveSteps f.stride ⟨j,index⟩
    ⟨(f.reserve.eval m r).val,digit⟩ fixture m size limit mounted
  have key : ((j*f.stride:ℕ):Word w)+f.reserve.eval m r =
      ((j*f.stride+(f.reserve.eval m r).val:ℕ):Word w) := by simp only [Nat.cast_add,Fin.cast_val_eq_self]
  change ((f.stock.eval m r)+(onBoundary addr (.inner p a j)
    (.lookup f.feedTable (.op .add (.lit (j*f.stride)) f.reserve)) (.lit 0)).eval m r).val=_
  rw [boundary_eval]
  by_cases paid : m (addr (.outer p a))=3
  · simp only [paid,ite_true,Expr.eval,RowOp.opcode,BinaryOp.eval,key,entry,innerAmount] at room ⊢
    exact add_value _ _ room
  · simp [paid,innerAmount,Expr.eval]

/-- Buying nothing discharges a zero increment without requiring the reserve bank to be read. -/
theorem inner_idle (f : CommodityColumn) (c : Mesh) (p a j : ℕ) (addr : Attempt → ℕ)
    (m : Memory w) (r : Word w) (idle : m (addr (.outer p a))≠3) :
    ((total addr (.inner p a j) (f.feed c (.inner p a j))).eval m r).val=(f.stock.eval m r).val := by
  change ((f.stock.eval m r)+(onBoundary addr (.inner p a j)
    (.lookup f.feedTable (.op .add (.lit (j*f.stride)) f.reserve)) (.lit 0)).eval m r).val=_
  rw [boundary_eval]
  simp [idle,Expr.eval]

end Hierarchy.ProtocolRAM.Calendar.CommodityColumn

end OAI

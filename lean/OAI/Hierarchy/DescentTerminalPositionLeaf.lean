import OAI.Hierarchy.DescentTerminalLeafHeap
import OAI.Hierarchy.DescentTerminalPositionDecoded

namespace OAI
/-! # One paid issue for each complete booked row, including gaps and the nullary row -/
namespace Hierarchy.DescentTerminalSiteShelves
open DescentTerminalRowBooks DescentTerminalHeaderScatter Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {q t H N A w V pool bits : ℕ}
local notation "C" => Control q t H N A w V

/-- The event bank is exactly the newly computed gather, followed by the fixed site-book table.
Each target is its own paid row, so the physical scatter has one writer per row. -/
theorem merge (tape : Fin pool→Option C) (L : DescentTerminalLeafFold.Layout) (m : Memory bits) (srcBase : ℕ)
    (cell : L.cells.Fits bits srcBase) (space : pool+1≤L.cells.size) (top : srcBase<2^bits)
    (rows : (DescentTerminalLeafFold.row L).Fits bits L.cells.base)
    (half : ∀(i : Fin pool) (j : Fin 2),L.half.read m ((field i j).val:Word bits)=(i.val:Word bits))
    (identity : ∀i : Fin pool,L.home.read m (i.val:Word bits)=(i.val:Word bits))
    (weightAt : ∀i : Fin pool,L.weight.read m (L.event.read m (i.val:Word bits))=(DescentTerminalLeafFold.code (tape i):Word bits))
    (i : Fin pool) : L.cells.read (DescentTerminalLeafFold.reduced L m pool pool srcBase) (i.val:Word bits)=
      (DescentTerminalLeafFold.code (tape i):Word bits) := by
  let clear:=DescentTerminalLeafFold.cleared L pool m
  let record:=DescentTerminalLeafFold.selected L m pool pool
  have same {x} (b:x<L.cells.base) : clear x=m x :=
    DescentTerminalChipRuntime.image_low m L.cells.base (pool+1) (.lit 0) b
  have lo : (DescentTerminalLeafFold.low L).Fits bits L.cells.base:=rows.2.2.1
  have hi : (DescentTerminalLeafFold.high L).Fits bits L.cells.base:=rows.2.2.2
  have first (k : Fin pool) : (record k).1.val=L.cells.base+k.val := by
    have add : (DescentTerminalLeafFold.address L).eval m ((field k 0).val:Word bits)=((L.cells.base+k.val:ℕ):Word bits) := by
      simp [DescentTerminalLeafFold.address,Expr.eval,RowOp.opcode,BinaryOp.eval,half,identity,Nat.cast_add]
    have native:=bounded_exact L.cells (DescentTerminalLeafFold.address L) m ((field k 0).val:Word bits) cell top
      (k.isLt.trans_le (by omega)) add
    have reg := eval_below (DescentTerminalLeafFold.low L) ((field k 0).val:Word bits)
      m clear lo (fun a h=>same h)
    have raw : (record k).1 = ((L.cells.base+k.val:ℕ):Word bits) := reg.trans (native.trans add)
    have fits : L.cells.base+k.val<2^bits := by
      have bound := cell.2.2
      have valid := k.isLt
      omega
    exact (congrArg Fin.val raw).trans (Fin.val_cast_of_lt fits)
  have values (k : Fin pool) : ((record k).2.val:Word bits)=(DescentTerminalLeafFold.code (tape k):Word bits) := by
    rw [Fin.cast_val_eq_self]
    change (DescentTerminalLeafFold.high L).eval clear _=_
    rw [eval_below _ _ m _ hi (fun a h=>same h)]
    simpa [DescentTerminalLeafFold.high,Expr.eval,half] using weightAt k
  rw [DescentTerminalDenseHeaderRAM.bank_nat _ cell (by omega)]
  have atZero : DescentTerminalLeafFold.staged L pool pool srcBase m (L.cells.base+i.val)=0:=by
    have early : L.cells.base+i.val<srcBase := by have bound:=cell.2.2; have valid:=i.isLt; omega
    have after := DescentTerminalChipRuntime.image_low clear srcBase (2*pool) (DescentTerminalLeafFold.row L) early
    have zero := DescentTerminalDenseHeaderRAM.at_image L.cells.base (.lit 0) m (i.castSucc : Fin (pool+1))
    exact after.trans zero
  change _+_=_
  rw [atZero,zero_add]
  change ((∑k:Fin pool,if k.val<pool ∧ (record k).1.val=L.cells.base+i.val then (record k).2.val else 0:ℕ):Word bits)=_
  simp only [Fin.is_lt,true_and,first,Nat.add_left_cancel_iff,←Fin.ext_iff]
  rw [Finset.sum_eq_single i]
  · simpa using values i
  · intro k _ ne;simp [ne]
  · simp

end
end Hierarchy.DescentTerminalSiteShelves

end OAI

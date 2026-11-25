import OAI.Hierarchy.DescentTerminalLeafHeap
import OAI.Hierarchy.DescentTerminalPrintedFieldsRAM

namespace OAI
/-! # Reading a scalar header from the merged cells of the terminal shelf -/
namespace Hierarchy.DescentTerminalPackedLeaves
open DescentTerminalPrintedFields DescentTerminalRowBooks Computability.VPVNP.BurstRAM PrivateRAM
open DescentTerminalHeaderScatter ThreeFlat.RAM
open PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {q t H N A w V pool n bits : ℕ}
local notation "u" => capacity q t H N A w V
variable (tape : Fin pool→Option (Control q t H N A w V))

theorem print_merged (L : DescentTerminalLeafFold.Layout) (m : Memory bits) (srcBase out : ℕ) (_pos : 0<bits)
    (source : ∀i : Fin pool,L.cells.read (DescentTerminalLeafFold.reduced L m pool n srcBase) (i.val:Word bits)=
      (DescentTerminalLeafFold.code (tape i):Word bits))
    (cell : L.cells.Fits bits srcBase) (space : pool+1≤L.cells.size) (top : srcBase<2^bits)
    (same : L.occupancy=L.cells) (beforeTable : L.table.Fits bits L.cells.base)
    (totalFit : (u).total≤2^bits) (occupied : ∀i c,tape i=some c → c.1.val≠0)
    (headers : ∀j : Fin (u).total,L.table.read m (j.val:Word bits)=
      ((headerTable q t H N A w V)[j.val]'(by simpa only [headerTable,List.length_ofFn] using j.isLt):Word bits))
    (i : Fin pool) : DescentTerminalLeafFold.final L m pool n srcBase out (out+i.val)=
      (DescentTerminalPrintedFieldsRAM.expected (tape i):Word bits) := by
  let reduced:=DescentTerminalLeafFold.reduced L m pool n srcBase
  have frame (a : ℕ) (early : a<L.cells.base) : reduced a=m a := by
    have ahead : a<srcBase := by have := cell.2.2; omega
    calc
      reduced a = DescentTerminalLeafFold.final L m pool n srcBase srcBase a :=
        (DescentTerminalChipRuntime.image_low reduced srcBase pool (DescentTerminalLeafFold.lookup L) ahead).symm
      _ = m a := DescentTerminalLeafFold.before L m srcBase srcBase pool n cell top le_rfl early
  have bank (b:Bank) (small:b.Fits bits L.cells.base) (j:Word bits) : b.read reduced j=b.read m j := by
    apply frame
    have:=small.2.2;have:=Nat.mod_lt j.val small.1;omega
  have read:=source i
  change image out pool (DescentTerminalLeafFold.lookup L) reduced (out+i.val)=_
  rw [DescentTerminalDenseHeaderRAM.at_image]
  cases h:tape i with
  | none=>
    have emptyCell : L.cells.read reduced (i.val:Word bits)=0 := by
      simpa [h,DescentTerminalLeafFold.code] using read
    simp [DescentTerminalLeafFold.lookup,same,Expr.eval,DescriptorExpr.Comparison.test,emptyCell,
      DescentTerminalPrintedFieldsRAM.expected]
  | some c=>
    let v:=serial u (digits (emit c))
    have hcount : 0<c.1.val:=Nat.pos_of_ne_zero (occupied i c h)
    have stride : 0<(DescentTerminalPrintedFieldsRAM.strides u).a:=by
      unfold DescentTerminalPrintedFieldsRAM.strides capacity
      dsimp
      positivity
    have positive : 0<v.val:=by
      rw [show v.val=(serial u (digits (emit c))).val from rfl,DescentTerminalPrintedFieldsRAM.serial_val]
      have head : (digits (emit c)).1.val=c.1.val:=rfl
      rw [head]
      exact Nat.add_pos_left (Nat.mul_pos hcount stride) _
    have nz : (v.val:Word bits)≠0:=by
      intro eqn
      have equal:=congrArg Fin.val eqn
      simp [Fin.val_cast_of_lt (v.isLt.trans_le totalFit)] at equal
      omega
    have hc : L.cells.read reduced (i.val:Word bits)=(v.val:Word bits):=by
      simpa [DescentTerminalLeafFold.code,h,v] using read
    have word:=headers v
    rw [show v=serial u (digits (emit c)) from rfl,table_actual c] at word
    simp only [DescentTerminalLeafFold.lookup,same,Expr.eval,DescriptorExpr.Comparison.test,hc,
      Nat.cast_zero,beq_iff_eq,nz,ite_false,bank _ beforeTable]
    simpa [v,DescentTerminalPrintedFieldsRAM.expected,h] using word

end
end Hierarchy.DescentTerminalPackedLeaves

end OAI

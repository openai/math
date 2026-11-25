import OAI.Hierarchy.ProtocolRAMCalendarPrefixDebits

namespace OAI
/-! # Physical unused catalyst widths in every dated replay page -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.PrefixReserve
open Computability.VPVNP.BurstRAM PrivateRAM CatalystArchive
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped BigOperators Classical Fin.CommRing
variable {W count payload : ℕ}

/-- Both operands are live words on the permanent page for this date. -/
def leftExpr (L : PrefixWidths.Layout count) (old : RouteSettlement.Banks) (j : ℕ) (rowExpr : Expr) : Expr :=
  .op .sub (.lookup (banks L old j).reserved rowExpr) (.lookup (banks L old j).used rowExpr)

theorem leftExpr_work (L : PrefixWidths.Layout count) (old : RouteSettlement.Banks) (j : ℕ) (rowExpr : Expr) :
    (leftExpr L old j rowExpr).work=2*rowExpr.work+11 := by
  change (rowExpr.work+5)+(rowExpr.work+5)+1=_
  omega

theorem leftExpr_fits (L : PrefixWidths.Layout count) (old : RouteSettlement.Banks) (j : ℕ)
    (rowExpr : Expr) (out : ℕ) (ready : rowExpr.Fits W out) (room : (L.bank (2*j+1)).base+2^L.bits≤out)
    (wide : 2^L.bits<2^W) : (leftExpr L old j rowExpr).Fits W out := by
  have order : (L.bank (2*j)).base≤(L.bank (2*j+1)).base:=by
    change L.archive+2*j*(2^L.bits+1)≤L.archive+(2*j+1)*(2^L.bits+1)
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  exact ⟨⟨⟨Nat.two_pow_pos _,wide,(Nat.add_le_add_right order _).trans room⟩,ready⟩,
    ⟨⟨Nat.two_pow_pos _,wide,room⟩,ready⟩⟩

/-- The last clause of `after_widths` directly decodes the cumulative
ordered archive at this rowExpr. Funding comes from the actual issued receipts. -/
theorem leftExpr_read (c : Mesh) (issued : Attempt→Entry count payload)
    (L : PrefixWidths.Layout count) (old : RouteSettlement.Banks) (j : ℕ)
    (m : Memory W) (rowExpr : Expr) (r : Word W) (i : Fin count)
    (wide : count≤2^W) (index : rowExpr.eval m r=(i.val:Word W))
    (pages : (m ((banks L old j).used.base+i.val)).val=
        (∑ s : Fin (recordCount c issued),if ((rank c issued).symm s).1.val<j ∧ site c issued s=i then debit c issued s else 0) ∧
      (m ((banks L old j).reserved.base+i.val)).val=fuel c*payload) :
    (leftExpr L old j rowExpr).eval m r=
      ((fuel c*payload-used (site c issued) (debit c issued) (countAt c issued j) i:ℕ):Word W) := by
  have cell (b : Bank) (size : count≤b.size) :
      b.read m (i.val:Word W)=m (b.base+i.val) := by
    simp only [Bank.read,Fin.val_cast_of_lt (i.isLt.trans_le wide),Nat.mod_eq_of_lt (i.isLt.trans_le size)]
  have usedPage : m ((banks L old j).used.base+i.val)=
      ((used (site c issued) (debit c issued) (countAt c issued j) i):Word W) := by
    rw [chronological c issued]
    exact (Fin.cast_val_eq_self _).symm.trans (congrArg Nat.cast pages.1)
  have limitPage : m ((banks L old j).reserved.base+i.val)=((fuel c*payload:ℕ):Word W) :=
    (Fin.cast_val_eq_self _).symm.trans (congrArg Nat.cast pages.2)
  simp only [leftExpr,Expr.eval,RowOp.opcode,BinaryOp.eval,index,
    cell (banks L old j).reserved L.covered,cell (banks L old j).used L.covered,
    limitPage,usedPage,Nat.cast_sub (funded c issued j i)]

theorem leftExpr_val (c : Mesh) (issued : Attempt→Entry count payload)
    (L : PrefixWidths.Layout count) (old : RouteSettlement.Banks) (j : ℕ)
    (m : Memory W) (rowExpr : Expr) (r : Word W) (i : Fin count)
    (wide : count≤2^W) (reserveRoom : fuel c*payload<2^W) (index : rowExpr.eval m r=(i.val:Word W))
    (pages : (m ((banks L old j).used.base+i.val)).val=
        (∑ s : Fin (recordCount c issued),if ((rank c issued).symm s).1.val<j ∧ site c issued s=i then debit c issued s else 0) ∧
      (m ((banks L old j).reserved.base+i.val)).val=fuel c*payload) :
    ((leftExpr L old j rowExpr).eval m r).val=
      fuel c*payload-used (site c issued) (debit c issued) (countAt c issued j) i := by
  have word:=leftExpr_read c issued L old j m rowExpr r i wide index pages
  exact (congrArg Fin.val word).trans (Fin.val_cast_of_lt ((Nat.sub_le ..).trans_lt reserveRoom))

end Hierarchy.ProtocolRAM.Calendar.PrefixReserve
end

end OAI

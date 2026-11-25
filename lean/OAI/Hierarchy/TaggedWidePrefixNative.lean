import OAI.Hierarchy.TaggedWideLocalPrefix
import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # The RAM computes local bond starts using constant-degree opposite-side comparisons -/

noncomputable section
namespace Hierarchy.ProtocolRAM.LocalPrefix
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing BigOperators Classical

structure Columns where
  ordinal : Expr
  opposite : Expr
  width : Expr

def term (o head : Columns) : Expr :=
  .branch .lt o.ordinal head.ordinal (.branch .eq o.opposite head.opposite o.width (.lit 0)) (.lit 0)

def total : (D : ℕ) → (Fin D → Expr) → Expr
  | 0,_=>.lit 0
  | d+1,e=>.op .add (e 0) (total d (fun i=>e i.succ))

theorem total_eval {W : ℕ} (D : ℕ) (e : Fin D → Expr) (m : Memory W) (r : Word W) :
    (total D e).eval m r=∑i,(e i).eval m r := by
  induction D with
  | zero=>simp [total,Expr.eval]
  | succ d ih=>rw [Fin.sum_univ_succ]
               simp [total,Expr.eval,RowOp.opcode,BinaryOp.eval,ih]

def expr {D : ℕ} (row : Fin D → Columns) (head : Columns) := total D (fun i=>term (row i) head)

theorem read {W n g D : ℕ} (row : Fin D → Columns) (head : Columns) (m : Memory W) (r : Word W)
    (key : Fin n → Fin g) (width : Fin n→ℕ) (i : Fin n)
    (place : {j : Fin n // 0<width j ∧ key j=key i} ↪ Fin D)
    (headOrd : (head.ordinal.eval m r).val=i.val)
    (localRows : ∀j,((row (place j)).ordinal.eval m r).val=j.val.val ∧
      ((row (place j)).opposite.eval m r).val=(head.opposite.eval m r).val ∧
      ((row (place j)).width.eval m r).val=width j.val)
    (blanks : ∀q,q∉Set.range place → ((row q).opposite.eval m r).val≠(head.opposite.eval m r).val ∨
      ((row q).width.eval m r).val=0) :
    (expr row head).eval m r=(TaggedShorterCommonScan.earlier key width i.val (key i):Word W) := by
  let ord := fun q=>((row q).ordinal.eval m r).val
  let other := fun q=>((row q).opposite.eval m r).val
  let value := fun q=>((row q).width.eval m r).val
  rw [←Tagged.PassiveWindow.local_prefix key width i (key i) ord other value
    (head.opposite.eval m r).val place localRows blanks,Nat.cast_sum,expr,total_eval]
  apply Finset.sum_congr rfl
  intro q _
  by_cases earlier : ord q < i.val <;> by_cases same : other q=(head.opposite.eval m r).val <;>
    simp_all [term,Expr.eval,Comparison.test,ord,other,value,←Fin.ext_iff,Fin.lt_def]

end Hierarchy.ProtocolRAM.LocalPrefix

end
end OAI

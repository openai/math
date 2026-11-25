import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Hierarchy.DescentTerminalBookROM

namespace OAI
/-! # One cheap shared-table read per allocated row to issue its actual local name list -/
namespace Hierarchy.DescentTerminalLocalPortBook
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentTerminalBinPack DescentTerminalRouteRows
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {G V M A a W q w n S : ℕ}

structure Gather where
  occupied : Bank
  site : Bank
  head : Bank
  localRow : Bank
  homeOffset : Bank
  low : Bank
  high : Bank
  menu : Bank
  names : Bank

namespace Gather
def raw (L : Gather) : Expr := .lookup L.menu (.op .add (.lookup L.head (.lookup L.site .row))
  (.op .add (.lookup L.low (.lookup L.localRow .row)) (.lookup L.high (.lookup L.homeOffset (.lookup L.site .row)))))
def load (L : Gather) : Expr := .branch .eq (.lookup L.occupied .row) (.lit 0) (.lit 0) (raw L)
def program (L : Gather) (w n : ℕ) := scan w L.names.base n (load L)
def output (L : Gather) (n : ℕ) (m : Memory w) := image L.names.base n (load L) m
theorem run (L : Gather) (n : ℕ) (m : Memory w) (fit : (load L).Fits w L.names.base)
    (room : L.names.base+n<2^w) : (program L w n).Exec m (output L n m) (4+n*(2*(load L).work+4)) ∧
      CheapCode (program L w n) :=
  ⟨scan_exec L.names.base n (load L) m fit room,scan_cheap w L.names.base n (load L)⟩

abbrev Where (S W : ℕ) := Option (Fin S×Fin W)
structure Inputs (L : Gather) (books : Fin S→Book G V M A a) (owner : Fin S→Fin W)
    (span : Fin n→Where S W) (q : ℕ) (m : Memory w) : Prop where
  occupied : ∀i:Fin n,L.occupied.read m (i.val:Word w)=
    (if (span i).isSome then 1 else 0)
  whereAt : ∀(i:Fin n) (v:Fin S) (r:Fin W),span i=some (v,r) →
    L.site.read m (i.val:Word w)=(v.val:Word w) ∧ L.localRow.read m (i.val:Word w)=(r.val:Word w)
  home : ∀v:Fin S,L.homeOffset.read m (v.val:Word w)=((owner v).val:Word w)
  book : ∀v:Fin S,L.head.read m (v.val:Word w)=((books v).bytes.val:Word w)
  low : ∀r:Fin W,L.low.read m (r.val:Word w)=((Book.Bytes G V M A a*r.val:ℕ):Word w)
  high : ∀r:Fin W,L.high.read m (r.val:Word w)=((W*Book.Bytes G V M A a*r.val:ℕ):Word w)
  table : ∀i:Fin (W*(W*Book.Bytes G V M A a)),L.menu.read m (i.val:Word w)=
    ((Book.menu (G:=G) (V:=V) (M:=M) (A:=A) (a:=a) q i).val:Word w)

private theorem at_row (L : Gather) (n : ℕ) (m : Memory w) (i : Fin n) :
    L.output n m (L.names.base+i.val)=L.load.eval m (i.val:Word w) := by simp [output,image,fillSegment,i.isLt,Nat.cast_add]

theorem read (L : Gather) (books : Fin S→Book G V M A a) (owner : Fin S→Fin W)
    (span : Fin n→Where S W) (m : Memory w) (inputs : Inputs L books owner span q m) (pos : 0<w) (i : Fin n) :
    output L n m (L.names.base+i.val)=
      (span i).elim 0 (fun z=>((Book.emit (books z.1) q z.2.val (owner z.1)).val:Word w)) := by
  rw [at_row]
  have one : (1:Word w)≠0 := by have fact : 1<2^w:=Nat.one_lt_two_pow_iff.mpr (by omega);exact fun e=>by have h:=congrArg Fin.val e;simp [Nat.mod_eq_of_lt fact] at h
  cases hi:span i with
  | none=>simp [load,Expr.eval,inputs.occupied i,hi,Comparison.test]
  | some z=>
    rcases z with ⟨v,r⟩
    have loc:=inputs.whereAt i v r hi
    have addr :=congrArg (fun z:ℕ=>(z:Word w)) (Book.request_val (books v) (owner v) r)
    simp [] at addr
    simp [load,raw,Expr.eval,inputs.occupied i,hi,one,loc.1,loc.2,inputs.home,inputs.book,inputs.low,inputs.high,
      RowOp.opcode,BinaryOp.eval,Comparison.test,←add_assoc]
    rw [←addr,inputs.table,Book.menu_read]

end Gather
end
end Hierarchy.DescentTerminalLocalPortBook

end OAI

import OAI.Hierarchy.DescentTerminalBookROM
import OAI.Hierarchy.DescentTerminalFieldPart
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Publishing the literal six columns of a compact terminal incidence record -/
namespace Hierarchy.DescentTerminalLocalPortBook
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
namespace Book
variable {G V M A a : ℕ}
def columns (u : Book G V M A a) : Fin 6→ℕ :=
  ![u.groupCount.val,u.nodeCount.val,(flat u.groupSize).val,(flat u.nodeArity).val,(portFile u.portName).val,(portFile u.operand).val]

theorem bytes_val (u : Book G V M A a) :
    u.bytes.val=∑i,columns u i*strides G V M A a i := by
  simp [bytes,cols,packCols,finProdFinEquiv,Equiv.coe_fn_mk,columns,strides,capacities,Fin.sum_univ_succ]
  ring
def slot (u : Book G V M A a) (i : Fin 6) : Fin (capacities G V M A a i) :=
  ⟨columns u i,by
    have groups : u.groupCount.val ≤ G := Nat.le_of_lt_succ u.groupCount.isLt
    have nodes : u.nodeCount.val ≤ V := Nat.le_of_lt_succ u.nodeCount.isLt
    fin_cases i <;> simp [columns,capacities,groups,nodes]⟩

variable {w S : ℕ}
abbrev Parts := Fin 6→DescentTerminalPrintedFieldsRAM.Part
def expression (L : Parts) : Expr :=
  .op .add (L 0).fetch (.op .add (L 1).fetch (.op .add (L 2).fetch
  (.op .add (L 3).fetch (.op .add (L 4).fetch (L 5).fetch))))
def price (L : Parts) (n : ℕ) := 4+n*(2*(expression L).work+4)
theorem fees (L : Parts) (n : ℕ) : price L n ≤4+192*n := by
  have a : (expression L).work=77:=rfl
  unfold price; rw [a];omega

structure Issued (L : Parts) (tape : Fin S→Book G V M A a) (m : Memory w) : Prop where
  source : ∀(i : Fin S) (f : Fin 6),(L f).source.read m (i.val:Word w)=((columns (tape i) f):Word w)
  values : ∀(f : Fin 6) (d : Fin (capacities G V M A a f)),
    (L f).weights.read m (d.val:Word w)=((d.val*strides G V M A a f:ℕ):Word w)

theorem numeric (L : Parts) (tape : Fin S→Book G V M A a) (m : Memory w) (issued : Issued L tape m) (i : Fin S) :
    (expression L).eval m (i.val:Word w)=((tape i).bytes.val:Word w) := by
  have column (f:Fin 6) : (L f).fetch.eval m (i.val:Word w)=
      ((columns (tape i) f*strides G V M A a f:ℕ):Word w):=by
    simp only [DescentTerminalPrintedFieldsRAM.Part.fetch,Expr.eval,issued.source]
    exact issued.values f (slot (tape i) f)
  rw [bytes_val]
  simp only [expression,Expr.eval,RowOp.opcode,BinaryOp.eval]
  repeat' rw [column]
  simp [Fin.sum_univ_succ,Nat.cast_add]

theorem publish (L : Parts) (m : Memory w) (out : ℕ) (low : (expression L).Fits w out) (room : out+S<2^w)
    (tape : Fin S→Book G V M A a) (issued : Issued L tape m) :
    (scan w out S (expression L)).Exec m (image out S (expression L) m) (price L S)
      ∧ CheapCode (scan w out S (expression L)) ∧ ∀i:Fin S,image out S (expression L) m (out+i.val)=((tape i).bytes.val:Word w) :=
  ⟨scan_exec out S (expression L) m low room,scan_cheap w out S (expression L),fun i=>(by
    simpa [image,fillSegment,i.isLt,Nat.cast_add] using numeric L tape m issued i)⟩

end Book
end
end Hierarchy.DescentTerminalLocalPortBook

end OAI

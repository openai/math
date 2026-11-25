import OAI.Hierarchy.DescentTerminalFieldPart
import OAI.Hierarchy.DescentTerminalWeightWords
import OAI.Hierarchy.DescentTerminalPrintedFields
import OAI.Hierarchy.DescentTerminalScanReads

namespace OAI
/-! # Printing a scalar header from six reached local field columns in one RAM pass -/
namespace Hierarchy.DescentTerminalPrintedFieldsRAM
open DescentTerminalRowBooks DescentTerminalPrintedFields Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Fin.CommRing Classical
noncomputable section

structure Layout where
  occupancy : Bank
  a : Part
  b : Part
  c : Part
  d : Part
  e : Part
  f : Part
  table : Bank

def row (L : Layout) : Expr :=
  .branch .eq (.lookup L.occupancy .row) (.lit 0) (.lit 0)
    (.lookup L.table (.op .add L.a.fetch (.op .add L.b.fetch (.op .add L.c.fetch
      (.op .add L.d.fetch (.op .add L.e.fetch L.f.fetch))))))

def program (L : Layout) (bits out n : ℕ) := scan bits out n (row L)

theorem cheap (L : Layout) (bits out n : ℕ) : CheapCode (program L bits out n) := @scan_cheap _ _ _ _


variable {bits out pool q t H N A w V : ℕ}
def Part.Reads (b : Part) (m : Memory bits) {k : ℕ} (v : Fin pool→Fin k) (stride : ℕ) :=
  (∀i : Fin pool,b.source.read m (i.val:Word bits)=((v i).val:Word bits)) ∧
  ∀j : Fin k,b.weights.read m (j.val:Word bits)=((j.val*stride:ℕ):Word bits)

theorem part_read (b : Part) (m : Memory bits) {k : ℕ} (v : Fin pool→Fin k) (stride : ℕ)
    (h : b.Reads m v stride) (i : Fin pool) :
    b.fetch.eval m (i.val:Word bits)=(((v i).val*stride:ℕ):Word bits) := by
  simp [Part.fetch,Expr.eval,h.1,h.2]

def strides (u : Six) : Six :=
  ⟨u.b*(u.c*(u.d*(u.e*u.f))),u.c*(u.d*(u.e*u.f)),u.d*(u.e*u.f),u.e*u.f,u.f,1⟩

theorem serial_val (u : Six) (v : Digits u) :
    (serial u v).val=v.1.val*(strides u).a+(v.2.1.val*(strides u).b+
      (v.2.2.1.val*(strides u).c+(v.2.2.2.1.val*(strides u).d+
        (v.2.2.2.2.1.val*(strides u).e+v.2.2.2.2.2.val*(strides u).f)))) := by
  change v.2.2.2.2.2.val+u.f*v.2.2.2.2.1.val+(u.e*u.f)*v.2.2.2.1.val+
    (u.d*(u.e*u.f))*v.2.2.1.val+(u.c*(u.d*(u.e*u.f)))*v.2.1.val+
    (u.b*(u.c*(u.d*(u.e*u.f))))*v.1.val=_
  unfold strides
  ring

local notation "u" => capacity q t H N A w V
local notation "C" => Control q t H N A w V
def vacant (q t H N A w V : ℕ) : Control q t H N A w V := ⟨0,Fin.elim0⟩
def expected (z : Option C) : ℕ := (z.map fun c=>(DescentTerminalScalarHeader.encode c).val+1).getD 0
def fields (tape : Fin pool→Option C) (i : Fin pool) := digits (emit ((tape i).getD (vacant q t H N A w V)))

/-- The mask is the existing bin/row membership bit; raw fields of a
vacant row are ignored. The five mixed-radix multiplications and the
last identity field use fixed small lookup columns. -/
structure Inputs (L : Layout) (m : Memory bits) (tape : Fin pool→Option C) : Prop where
  mask : ∀i,L.occupancy.read m (i.val:Word bits)=((if (tape i).isSome then 1 else 0:ℕ):Word bits)
  a : L.a.Reads m (fun i=>(fields tape i).1) (strides u).a
  b : L.b.Reads m (fun i=>(fields tape i).2.1) (strides u).b
  c : L.c.Reads m (fun i=>(fields tape i).2.2.1) (strides u).c
  d : L.d.Reads m (fun i=>(fields tape i).2.2.2.1) (strides u).d
  e : L.e.Reads m (fun i=>(fields tape i).2.2.2.2.1) (strides u).e
  f : L.f.Reads m (fun i=>(fields tape i).2.2.2.2.2) (strides u).f
  table : ∀j : Fin (u).total,L.table.read m (j.val:Word bits)=
    ((headerTable q t H N A w V)[j.val]'(by simpa only [headerTable,List.length_ofFn] using j.isLt):Word bits)

theorem row_eval (L : Layout) (m : Memory bits) (tape : Fin pool→Option C)
    (inputs : Inputs L m tape) (pos : 0<bits) (i : Fin pool) :
    (row L).eval m (i.val:Word bits)=(expected (tape i):Word bits) := by
  cases h : tape i with
  | none=>simp [row,Expr.eval,DescriptorExpr.Comparison.test,inputs.mask,h,expected]
  | some c=>
    have lookup:=inputs.table ((serial u) (digits (emit c)))
    rw [table_actual c] at lookup
    have one : (1:Word bits)≠0 := by
      have enough : 1<2^bits := Nat.one_lt_pow (Nat.ne_of_gt pos) (by decide)
      intro eqn
      have vals:=congrArg Fin.val eqn
      change 1%(2^bits)=0 at vals
      simp [Nat.mod_eq_of_lt enough] at vals
    simp only [row,Expr.eval,DescriptorExpr.Comparison.test,inputs.mask,h,Option.isSome_some,ite_true,Nat.cast_one,Nat.cast_zero,
      beq_iff_eq,one,ite_false,RowOp.opcode,BinaryOp.eval,part_read _ _ _ _ inputs.a i,
      part_read _ _ _ _ inputs.b i,part_read _ _ _ _ inputs.c i,part_read _ _ _ _ inputs.d i,
      part_read _ _ _ _ inputs.e i,part_read _ _ _ _ inputs.f i,←Nat.cast_add,←serial_val]
    simpa [fields,h,expected,Nat.ne_of_gt pos] using lookup

theorem run (L : Layout) (m : Memory bits) (tape : Fin pool→Option C) (inputs : Inputs L m tape)
    (fit : (row L).Fits bits out) (room : out+pool<2^bits) (pos : 0<bits) :
    (program L bits out pool).Exec m (image out pool (row L) m) (4+188*pool) ∧
      (∀i : Fin pool,image out pool (row L) m (out+i.val)=(expected (tape i):Word bits)) := by
  refine ⟨?_,fun i=>(DescentTerminalDenseHeaderRAM.at_image out (row L) m i).trans (row_eval L m tape inputs pos i)⟩
  have work : 2*(row L).work+4=188 := rfl
  rw [show 4+188*pool=4+pool*(2*(row L).work+4) by rw [work,Nat.mul_comm pool 188]]
  exact @scan_exec bits out pool (row L) m fit room

end
end Hierarchy.DescentTerminalPrintedFieldsRAM

end OAI

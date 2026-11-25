import OAI.ThreeFlat.RAM.TraceAddressExpr

namespace OAI
/-! # Uniform native reader of address records stored outside a trace

A port ordinal selects one eleven-word record. The same fixed program tests
the physical row, forms its XOR address, saturates a subtraction, and
optionally returns one bit. The record and the port ordinal are runtime data.
-/

namespace ThreeFlat.RAM.TraceAddressReader

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr Diagonal.TraceAddressRecord
open scoped Fin.CommRing

variable {w k : ℕ}

/-- Public serialization. Columns eight and nine hold the bit flag and bit number. -/
def fields (R : Record) : Fin 11 → ℕ :=
  ![R.testStride,R.testBias,R.lo,R.hi,R.base,R.stride,R.mask,R.sub,
    R.bit.isSome.toNat,R.bit.getD 0,R.fallback]

def address (base port : ℕ) (j : Fin 11) := base+11*port+j.val

private def arg (i : Fin 3) : Term w k 3 := .result i
private def get (j : Fin 11) : Term w k 3 :=
  .load (.binary .add (.binary .add (arg 2)
    (.binary .mul (.literal 11) (arg 1))) (.literal (j.val : Word w)))

/-- Registers are the row number, the port number and the base of the records. -/
def program : Term w k 3 :=
  let row := arg 0
  let test := Term.binary .add (.binary .mul (get 0) row) (get 1)
  let num := Term.binary .add (get 4) (.binary .mul (get 5) (.binary .bitXor row (get 6)))
  let value := TraceAddressExpr.cut num (get 7)
  let bit := Term.binary .bitAnd (.binary .shiftRight value (get 9)) (.literal 1)
  let result := Term.select .lt (.literal 0) (get 8) bit value
  .select .lt test (get 2) (get 10) (.select .lt test (get 3) result (get 10))

private theorem get_eval (j : Fin 11) (words : Fin k → Word w) (m : Memory w) (vs : Fin 3 → Word w)
    (base port : ℕ) (hp : vs 1=(port : Word w)) (hb : vs 2=(base : Word w))
    (hl : address base port j<2^w) :
    (get j).eval words m vs = m (address base port j) := by
  have loc : (base : Word w)+11*(port : Word w)+(j.val : Word w) = (address base port j : Word w) := by
    simp [address]
  simp only [get,Term.eval_load,Term.eval_binary,Term.eval_literal,arg,Term.eval,hb,hp,
    BinaryOp.eval,loc, Fin.val_cast_of_lt hl]

theorem eval (R : Record) (v port base : ℕ) (hw : 0<w) (fit : R.Fits w v)
    (hl : base+11*port+10<2^w) (words : Fin k → Word w) (m : Memory w) (vs : Fin 3 → Word w)
    (r : vs 0=(v : Word w)) (p : vs 1=(port : Word w)) (b : vs 2=(base : Word w))
    (hmem : ∀ j : Fin 11, m (address base port j)=(fields R j : Word w)) :
    (program (w:=w) (k:=k)).eval words m vs = (R.eval v : Word w) := by
  have f (j : Fin 11) : (get j).eval words m vs=(fields R j : Word w) := by
    rw [get_eval j words m vs base port p b (by unfold address; have := j.isLt; omega),hmem]
  have run := TraceAddressExpr.program_eval R hw fit words m (fun _=>vs 0) r
  refine Eq.trans ?_ run
  have small : (0 : Word w)<1 := by
    change (0 : Word w).val<(1 : Word w).val
    have htwo : 1<2^w := by simpa using Nat.pow_lt_pow_right (by decide : 1<2) hw
    simp [Nat.mod_eq_of_lt htwo]
  have v0 : fields R 0=R.testStride := rfl
  have v1 : fields R 1=R.testBias := rfl
  have v2 : fields R 2=R.lo := rfl
  have v3 : fields R 3=R.hi := rfl
  have v4 : fields R 4=R.base := rfl
  have v5 : fields R 5=R.stride := rfl
  have v6 : fields R 6=R.mask := rfl
  have v7 : fields R 7=R.sub := rfl
  have v8 : fields R 8=R.bit.isSome.toNat := rfl
  have v9 : fields R 9=R.bit.getD 0 := rfl
  have v10 : fields R 10=R.fallback := rfl
  cases h : R.bit <;>
    simp only [program,TraceAddressExpr.program,TraceAddressExpr.test,TraceAddressExpr.num,
      TraceAddressExpr.selectBit,TraceAddressExpr.cut,TraceAddressExpr.lit,Term.eval_select,
      Term.eval_binary,Term.eval_literal,arg,Term.eval,f,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,h,Option.isSome,Option.getD,
      Bool.toNat_false,Bool.toNat_true,Nat.cast_zero,Nat.cast_one,Comparison.test,
      lt_self_iff_false,small,decide_true,decide_false,Bool.false_eq_true,ite_false,ite_true]

/-- Every field read takes the same number of instructions independently of its column. -/
private theorem get_binds (j : Fin 11) : (get (w:=w) (k:=k) j).binds=6 := by
  simp [get,arg,Term.load,Term.binary,Term.literal,Term.binds]

theorem program_binds_eq : (program (w:=w) (k:=k)).binds=185 := by
  simp [program,TraceAddressExpr.cut,TraceAddressExpr.lit,Term.binary,Term.select,Term.literal,
    arg,Term.binds,get_binds]

theorem program_binds : (program (w:=w) (k:=k)).binds≤300 := by rw [program_binds_eq]; decide

/-- Put the three operands of the record lookup at arbitrary caller locations. -/
def lookup {n : ℕ} (row port base : Term w k n) : Term w k n :=
  program.instantiate ![row,port,base]

theorem lookup_binds {n : ℕ} (row port base : Term w k n) :
    (lookup row port base).binds=185+row.binds+port.binds+base.binds := by
  simp [lookup,program_binds_eq,Fin.sum_univ_succ,Nat.add_assoc]

theorem lookup_eval {n : ℕ} (row index start : Term w k n) (R : Record) (v port base : ℕ)
    (hw : 0<w) (fit : R.Fits w v) (hl : base+11*port+10<2^w) (words : Fin k → Word w)
    (m : Memory w) (vs : Fin n → Word w) (r : row.eval words m vs=(v : Word w))
    (p : index.eval words m vs=(port : Word w)) (b : start.eval words m vs=(base : Word w))
    (hmem : ∀ j : Fin 11, m (address base port j)=(fields R j : Word w)) :
    (lookup row index start).eval words m vs=(R.eval v : Word w) := by
  rw [lookup,Term.eval_instantiate]
  exact eval R v port base hw fit hl words m _ r p b hmem

end ThreeFlat.RAM.TraceAddressReader

end OAI

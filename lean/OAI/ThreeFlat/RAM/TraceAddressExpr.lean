import OAI.ThreeFlat.Diagonal.TraceAddressRecord
import OAI.ThreeFlat.RAM.LiteralTable
import OAI.Computability.VPVNP.PrimedInputRAMOpcodeFields

namespace OAI
/-! # Native row-address calculation with bounded program length -/

namespace ThreeFlat.RAM.TraceAddressExpr

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr Diagonal.TraceAddressRecord
open scoped Fin.CommRing
variable {w k n : ℕ}

def lit (a : ℕ) : Term w k n := .literal (a : Word w)
@[simp] private theorem lit_eval (a : ℕ) (words : Fin k → Word w) (m : Memory w)
    (vs : Fin n → Word w) : (lit a).eval words m vs = (a : Word w) := Term.eval_literal ..
def test (R : Record) (x : Term w k n) : Term w k n :=
  .binary .add (.binary .mul (lit R.testStride) x) (lit R.testBias)
def num (R : Record) (x : Term w k n) : Term w k n :=
  .binary .add (lit R.base) (.binary .mul (lit R.stride) (.binary .bitXor x (lit R.mask)))
def cut (x y : Term w k n) : Term w k n :=
  .select .lt x y (lit 0) (.binary .sub x y)
def selectBit (j : Option ℕ) (x : Term w k n) : Term w k n :=
  match j with
  | none => x
  | some b => .binary .bitAnd (.binary .shiftRight x (lit b)) (lit 1)

/-- Input zero contains the unsigned physical row number. Every component of
the port record is fixed across all rows and is an instruction literal. -/
def program (R : Record) : Term w k 1 :=
  let x : Term w k 1 := .result 0
  let result := selectBit R.bit (cut (num R x) (lit R.sub))
  .select .lt (test R x) (lit R.lo) (lit R.fallback)
    (.select .lt (test R x) (lit R.hi) result (lit R.fallback))

theorem program_binds (R : Record) : (program (w:=w) (k:=k) R).binds ≤ 40 := by
  cases h : R.bit <;>
    simp [program,selectBit,h,cut,num,test,lit,Term.select,Term.binary,Term.literal,Term.binds]

private theorem cmp {x y : ℕ} (hx : x<2^w) (hy : y<2^w) :
    Comparison.lt.test (x : Word w) (y : Word w) = decide (x<y) := by
  simp [Comparison.test, Fin.lt_def, Fin.val_cast_of_lt hx, Fin.val_cast_of_lt hy]

private theorem cut_eval (x y : Term w k n) (words : Fin k → Word w) (m : Memory w)
    (vs : Fin n → Word w) {a b : ℕ} (ha : x.eval words m vs = (a : Word w))
    (hb : y.eval words m vs = (b : Word w)) (fa : a < 2^w) (fb : b < 2^w) :
    (cut x y).eval words m vs = ((a-b : ℕ) : Word w) := by
  simp only [cut, lit, Term.eval_select, Term.eval_binary, Term.eval_literal, ha, hb,
    cmp fa fb, decide_eq_true_eq]
  split_ifs with h
  · simp [Nat.sub_eq_zero_of_le h.le]
  · simp [BinaryOp.eval,Nat.cast_sub (Nat.le_of_not_gt h)]

theorem program_eval (R : Record) {v : ℕ} (hw : 0<w) (fit : R.Fits w v)
    (words : Fin k → Word w) (m : Memory w) (vs : Fin 1 → Word w) (arg : vs 0 = (v : Word w)) :
    (program R).eval words m vs = (R.eval v : Word w) := by
  let x : Term w k 1 := .result 0
  have tx : (test R x).eval words m vs = (R.test v : Word w) := by
    simp [test,lit,x,Term.eval,arg,BinaryOp.eval,Record.test]
  have nx : (num R x).eval words m vs = (R.numerator v : Word w) := by
    simp [num,lit,x,Term.eval,arg,BinaryOp.eval,Record.numerator,Fin.val_cast_of_lt fit.row,
      Fin.val_cast_of_lt fit.mask]
  have cx := cut_eval (num R x) (lit R.sub) words m vs nx (Term.eval_literal ..)
    fit.numerator fit.sub
  have sx : (selectBit R.bit (cut (num R x) (lit R.sub))).eval words m vs =
      ((match R.bit with | none => R.result v | some j => ((R.result v).testBit j).toNat) : ℕ) := by
    cases h : R.bit with
    | none => exact cx
    | some j =>
      have fj : j<2^w := by simpa [h] using fit.bit
      have fx : R.numerator v - R.sub < 2^w := (Nat.sub_le ..).trans_lt fit.numerator
      simp only [selectBit,Term.eval_binary,lit_eval,cx,Nat.cast_one]
      rw [Computability.VPVNP.PrimedInputRAM.Opcodes.readBit_word hw, Fin.val_cast_of_lt fx, Fin.val_cast_of_lt fj]
      change Computability.VPVNP.PrimedInputRAM.encodeBit w ((R.result v).testBit j) = _
      cases (R.result v).testBit j <;> rfl
  change (Term.select .lt (test R x) (lit R.lo) (lit R.fallback)
    (.select .lt (test R x) (lit R.hi) (selectBit R.bit (cut (num R x) (lit R.sub)))
       (lit R.fallback))).eval words m vs = _
  simp only [Term.eval_select,lit_eval,tx,sx,cmp fit.test fit.lo,cmp fit.test fit.hi,
    decide_eq_true_eq,Record.eval]
  by_cases lo : R.test v < R.lo
  · simp [lo,Nat.not_le_of_lt lo]
  · by_cases hi : R.test v < R.hi <;> simp [lo,hi,Nat.le_of_not_gt lo]; cases R.bit <;> rfl

end ThreeFlat.RAM.TraceAddressExpr

end OAI

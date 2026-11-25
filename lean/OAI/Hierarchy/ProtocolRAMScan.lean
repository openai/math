import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # Native word passes for the adaptive protocol controller -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing

/-- One contiguous column of words on the advised tape or in a preceding pass. -/
structure Bank where
  base : ℕ
  bits : ℕ

def Bank.size (b : Bank) := 2^b.bits

/-- A bounded lookup is total on malformed selector words as well as valid indices. -/
def Bank.read {w : ℕ} (b : Bank) (m : Memory w) (i : Word w) : Word w :=
  m (b.base + i.val % b.size)

/-- Every input column ends before the first address overwritten by this pass. -/
def Bank.Fits (b : Bank) (w out : ℕ) : Prop :=
  0 < b.size ∧ b.size < 2^w ∧ b.base + b.size ≤ out

/-- Native row expressions only use arithmetic and bit operations with small Boolean
implementations. Fixed packet coefficients use additions in the histogram controller. -/
inductive RowOp where
  | add | sub | mask

def RowOp.opcode : RowOp → BinaryOp
  | .add => .add
  | .sub => .sub
  | .mask => .bitAnd

/-- The row register supplies the current position in the output column. Lookup indices
may themselves be loaded from the input tape, for example a commodity or catalogue ID. -/
inductive Expr where
  | row
  | lit (v : ℕ)
  | lookup (bank : Bank) (index : Expr)
  | op (tag : RowOp) (x y : Expr)
  | branch (test : Comparison) (x y yes no : Expr)

def Expr.eval {w : ℕ} (m : Memory w) (row : Word w) : Expr → Word w
  | .row => row
  | .lit n => n
  | .lookup b i => b.read m (i.eval m row)
  | .op tag a b => tag.opcode.eval (a.eval m row) (b.eval m row)
  | .branch test a b yes no =>
      if test.test (a.eval m row) (b.eval m row) then yes.eval m row else no.eval m row

def Expr.Fits (w out : ℕ) : Expr → Prop
  | .row | .lit _ => True
  | .lookup b i => b.Fits w out ∧ i.Fits w out
  | .op _ x y => x.Fits w out ∧ y.Fits w out
  | .branch _ x y a b => x.Fits w out ∧ y.Fits w out ∧ a.Fits w out ∧ b.Fits w out

def Expr.compile (w out : ℕ) : Expr → Term w 0 1
  | .row => .binary .sub (.result 0) (.literal (out : Word w))
  | .lit n => .literal (n : Word w)
  | .lookup b i =>
      .load (.binary .add (.literal (b.base : Word w))
        (.binary .bitAnd (i.compile w out) (.literal ((b.size-1 : ℕ) : Word w))))
  | .op tag x y => .binary tag.opcode (x.compile w out) (y.compile w out)
  | .branch test x y yes no =>
      .select test (x.compile w out) (y.compile w out) (yes.compile w out) (no.compile w out)

def Expr.work : Expr → ℕ
  | .row => 2
  | .lit _ => 1
  | .lookup _ i => i.work + 5
  | .op _ x y => x.work + y.work + 1
  | .branch _ x y a b => x.work + y.work + a.work + b.work + 1

@[simp] theorem compile_binds (w out : ℕ) (e : Expr) :
    (e.compile w out).binds = e.work := by
  induction e <;> simp [Expr.compile,Expr.work,Term.load,Term.binary,Term.literal,
    Term.select,Term.binds,Term.binds_letThen,Term.binds_rename, *] <;> omega

private theorem bank_addr {w out : ℕ} (b : Bank) (fit : b.Fits w out) (room : out < 2^w)
    (i : Word w) :
    (BinaryOp.add.eval (b.base : Word w) (BinaryOp.bitAnd.eval i ((b.size-1 : ℕ) : Word w))).val =
      b.base + i.val % b.size := by
  obtain ⟨pos,small,low⟩ := fit
  have bound : b.base+i.val%b.size < 2^w := by
    have rem := Nat.mod_lt i.val pos
    omega
  have mask : b.size-1 < 2^w := by omega
  simp only [BinaryOp.eval,Fin.val_cast_of_lt mask]
  rw [show i.val &&& (b.size-1) = i.val % b.size from Nat.and_two_pow_sub_one_eq_mod _ _]
  change ((b.base : Word w) + (↑(i.val % b.size) : Word w)).val = _
  rw [← Nat.cast_add,Fin.val_cast_of_lt bound]

theorem eval_compile {w out : ℕ} (e : Expr) (m : Memory w) (a : Word w)
    (fit : e.Fits w out) (room : out < 2^w) :
    (e.compile w out).eval Fin.elim0 m (fun _ => a) = e.eval m (a - (out:Word w)) := by
  induction e with
  | row => simp [Expr.compile,Expr.eval,Term.eval,BinaryOp.eval]
  | lit => simp [Expr.compile,Expr.eval]
  | lookup b i ih =>
    simp only [Expr.compile,Term.eval_load,Term.eval_binary,Term.eval_literal,
      ih fit.2,bank_addr b fit.1 room,Expr.eval,Bank.read]
  | op o x y hx hy => simp only [Expr.compile,Term.eval_binary,Expr.eval,hx fit.1,hy fit.2]
  | branch test x y yes no hx hy ht hf =>
    simp only [Expr.compile,Term.eval_select,Expr.eval,hx fit.1,hy fit.2.1,ht fit.2.2.1,hf fit.2.2.2]

theorem eval_below {w out : ℕ} (e : Expr) (a : Word w) (m m' : Memory w)
    (fit : e.Fits w out) (same : ∀ j < out, m' j = m j) :
    e.eval m' a = e.eval m a := by
  induction e with
  | row | lit => rfl
  | lookup b i ih =>
    rw [Expr.eval,Expr.eval,ih fit.2]
    apply same
    obtain ⟨pos,_,lo⟩ := fit.1
    have h := Nat.mod_lt (i.eval m a).val pos
    omega
  | op o x y hx hy => simp only [Expr.eval,hx fit.1,hy fit.2]
  | branch test x y yes no hx hy ht hf =>
    simp only [Expr.eval,hx fit.1,hy fit.2.1,ht fit.2.2.1,hf fit.2.2.2]

/-- One scan overwrites exactly one dense column. The fixed code is shared across its rows.
The machine can start with arbitrary register values. -/
def scan (w out n : ℕ) (e : Expr) : Procedure w :=
  PhysicalInputPhases.writing (e.compile w out) Fin.elim0 out n

def image {w : ℕ} (out n : ℕ) (e : Expr) (m : Memory w) : Memory w :=
  fillSegment out n (fun addr => e.eval m ((addr : Word w) - (out : Word w))) m

theorem scan_exec {w : ℕ} (out n : ℕ) (e : Expr) (m : Memory w)
    (fit : e.Fits w out) (room : out+n < 2^w) :
    (scan w out n e).Exec m (image out n e m) (4+n*(2*e.work+4)) := by
  let val := fun (addr : ℕ) => e.eval m ((addr : Word w) - (out : Word w))
  have spec : (scan w out n e).Spec (·=m) (fun src after=>after=fillSegment out n val src)
      (4+n*(2*(e.compile w out).binds+4)) := PhysicalInputPhases.writing_spec (e.compile w out) Fin.elim0 out n room
    (·=m) val (by
      intro src eq a m' _ _ agree
      subst src
      rw [eval_compile e m' a fit (by omega)]
      simpa [val] using eval_below e (a-(out:Word w)) m m' fit (fun j hj => agree j (.inl hj)))
  rw [compile_binds] at spec
  intro P R K M pc reg pub exit installed data cfg start entry eqm
  subst start
  exact spec M pc reg pub exit installed data cfg m entry rfl


end Hierarchy.ProtocolRAM

end OAI

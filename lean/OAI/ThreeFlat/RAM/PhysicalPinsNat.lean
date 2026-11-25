import OAI.ThreeFlat.RAM.PhysicalPinsExpr
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Nat.Bitwise

namespace OAI
/-! # Natural-number verification of fixed descriptor expressions

The certificate checks subtraction and word operands only where the selected
descriptor calculation needs them. Reads at unused conditional branches may
address arbitrary memory. The native select still has its fixed instruction count.
-/

namespace ThreeFlat.RAM.PhysicalPinsExpr

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr
open scoped Fin.CommRing

variable {w n : ℕ}

def natOp (w : ℕ) : BinaryOp → ℕ → ℕ → ℕ
  | .add,x,y => x+y
  | .sub,x,y => x-y
  | .mul,x,y => x*y
  | .div,x,y => x/y
  | .mod,x,y => x%y
  | .bitAnd,x,y => x&&&y
  | .bitOr,x,y => x|||y
  | .bitXor,x,y => x^^^y
  | .shiftLeft,x,y => if y<w then x<<<y else 0
  | .shiftRight,x,y => if y<w then x>>>y else 0

def natTest : Comparison → ℕ → ℕ → Bool
  | .eq,x,y => decide (x=y)
  | .lt,x,y => decide (x<y)

def Formula.natural (w : ℕ) (data : Param → ℕ) (m : ℕ → ℕ) (vs : Fin n → ℕ) :
    Formula n → ℕ
  | .reg i => vs i
  | .lit a => a
  | .param i => data i
  | .op b x y => natOp w b (x.natural w data m vs) (y.natural w data m vs)
  | .cut x y => x.natural w data m vs - y.natural w data m vs
  | .load x => m (x.natural w data m vs)
  | .select q x y a b => if natTest q (x.natural w data m vs) (y.natural w data m vs) then
      a.natural w data m vs else b.natural w data m vs

/-- The hypotheses needed for natural and modular values of a binary opcode to agree. -/
def opFits (w : ℕ) : BinaryOp → ℕ → ℕ → Prop
  | .add,_,_ | .mul,_,_ => True
  | .sub,x,y => y ≤ x
  | _,x,y => x < 2^w ∧ y < 2^w

theorem op_cast (op : BinaryOp) (x y : ℕ) (fit : opFits w op x y) :
    op.eval (x : Word w) (y : Word w) = (natOp w op x y : Word w) := by
  cases op with
  | add | mul => simp [BinaryOp.eval,natOp]
  | sub => simpa [BinaryOp.eval,natOp] using (Nat.cast_sub (R := Word w) fit).symm
  | div | mod | bitAnd | bitOr | bitXor =>
    obtain ⟨hx,hy⟩ := fit
    simp [BinaryOp.eval,natOp,Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hy]
  | shiftLeft | shiftRight =>
    obtain ⟨hx,hy⟩ := fit
    by_cases h : y<w <;> simp [BinaryOp.eval,natOp,h,Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hy]

theorem test_cast (q : Comparison) (x y : ℕ) (hx : x<2^w) (hy : y<2^w) :
    q.test (x : Word w) (y : Word w) = natTest q x y := by
  cases q with
  | lt => simp [Comparison.test,natTest,Fin.lt_def,Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hy]
  | eq =>
    apply Bool.eq_iff_iff.mpr
    simp [Comparison.test,natTest,Fin.ext_iff,Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hy]

/-- A size check for formulas with total memory reads. -/
def Formula.Fits (w : ℕ) (data : Param → ℕ) (m : ℕ → ℕ) (vs : Fin n → ℕ) :
    Formula n → Prop
  | .reg _ | .lit _ | .param _ => True
  | .op o x y => x.Fits w data m vs ∧ y.Fits w data m vs ∧
      opFits w o (x.natural w data m vs) (y.natural w data m vs)
  | .cut x y => x.Fits w data m vs ∧ y.Fits w data m vs ∧
      x.natural w data m vs < 2^w ∧ y.natural w data m vs < 2^w
  | .load x => x.Fits w data m vs ∧ x.natural w data m vs < 2^w
  | .select q x y a b => x.Fits w data m vs ∧ y.Fits w data m vs ∧
      x.natural w data m vs < 2^w ∧ y.natural w data m vs < 2^w ∧
      (if natTest q (x.natural w data m vs) (y.natural w data m vs) then
        a.Fits w data m vs else b.Fits w data m vs)

theorem Formula.value_eq_natural (f : Formula n) (data : Param → ℕ) (m : ℕ → ℕ) (vs : Fin n → ℕ)
    (fit : f.Fits w data m vs) :
    f.value (fun p => (data p : Word w)) (fun j => (m j : Word w)) (fun i => (vs i : Word w)) =
      (f.natural w data m vs : Word w) := by
  induction f with
  | reg | lit | param => rfl
  | op o x y ix iy =>
    obtain ⟨hx,hy,h⟩ := fit
    simp only [Formula.value, Formula.natural, ix hx, iy hy, op_cast o _ _ h]
  | cut x y ix iy =>
    obtain ⟨hx,hy,lx,ly⟩ := fit
    simp only [Formula.value, Formula.natural, ix hx, iy hy, test_cast .lt _ _ lx ly,natTest,
      decide_eq_true_eq]
    split_ifs with h
    · rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt h),Nat.cast_zero]
    · exact op_cast .sub _ _ (le_of_not_gt h)
  | load x ih =>
    obtain ⟨hx,hl⟩ := fit
    simp only [Formula.value, Formula.natural, ih hx, Fin.val_cast_of_lt hl]
  | select q x y a b ix iy ia ib =>
    obtain ⟨hx,hy,lx,ly,hchosen⟩ := fit
    simp only [Formula.value, Formula.natural, ix hx, iy hy, test_cast q _ _ lx ly]
    cases h : natTest q (x.natural w data m vs) (y.natural w data m vs) <;>
      simp only [h, Bool.false_eq_true, ite_false, ite_true] at hchosen ⊢
    · exact ib hchosen
    · exact ia hchosen

end ThreeFlat.RAM.PhysicalPinsExpr

end OAI

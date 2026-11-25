import OAI.ThreeFlat.RAM.TickMemoryLayout
import OAI.ThreeFlat.RAM.DescriptorExpr
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Native addresses of the current group, chunk, and team slot -/

namespace ThreeFlat.RAM.TickClockWords

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr Diagonal.TickChronology
open scoped Fin.CommRing

variable {w k : ℕ}

/-- Unsigned saturating subtraction, including the opening/closing margins
outside the interval when the resulting address is ordinarily used. -/
def diff {n : ℕ} (x y : Term w k n) : Term w k n :=
  .select .lt x y (.literal 0) (.binary .sub x y)

private theorem eval_diff {n : ℕ} (x y : Term w k n) (p : Fin k → Word w) (m : Memory w)
    (v : Fin n → Word w) (i j : ℕ) (a : x.eval p m v = (i : Word w))
    (b : y.eval p m v = (j : Word w)) (hi : i < 2^w) (hj : j < 2^w) :
    (diff x y).eval p m v = ((i-j : ℕ) : Word w) := by
  simp only [diff,Term.eval_select,Term.eval_binary,Term.eval_literal,Comparison.test,BinaryOp.eval,a,b,
    decide_eq_true_eq,Fin.lt_def,Fin.val_cast_of_lt hi,Fin.val_cast_of_lt hj]
  by_cases h : i<j
  · simp [h,Nat.sub_eq_zero_of_le h.le]
  · simp [h,Nat.cast_sub (Nat.le_of_not_gt h)]

/-- The two registers hold the team and transition identifiers. Each output
bank has constant instruction count and works for all histories. -/
def expr (c : Clock) (a q : ℕ) : Fin 4 → Term w k 2 :=
  let team := Term.result 0
  let t := Term.result 1
  let delta := diff t (.literal (c.beginTick : Word w))
  let off := Term.binary .mod delta (.literal (c.groupDuration : Word w))
  ![Term.binary .div delta (.literal (c.groupDuration : Word w)),off,
    Term.binary .mul (.binary .mod t (.literal (c.chunks : Word w))) (.literal (a : Word w)),
    Term.binary .add (.binary .mul (diff off (.literal (c.chunks+1 : ℕ))) (.literal (q : Word w))) team]

theorem expr_binds (c : Clock) (a q : ℕ) (i : Fin 4) : (expr (w:=w) (k:=k) c a q i).binds ≤ 40 := by
  fin_cases i <;> simp [expr,diff,Term.select,Term.literal,Term.binary,Term.binds]

theorem expr_eval (c : Clock) (a q team t : ℕ) (p : Fin k → Word w) (m : Memory w)
    (i : Fin 4) (hd : c.groupDuration < 2^w) (hb : c.beginTick < 2^w) (ht : t < 2^w) :
    (expr c a q i).eval p m ![(team : Word w),(t : Word w)] = ((values c a q team t i : ℕ) : Word w) := by
  let vs : Fin 2 → Word w := ![team,t]
  let x : Term w k 2 := Term.result (1 : Fin 2)
  let delta := diff x (.literal (c.beginTick : Word w))
  let off := Term.binary .mod delta (.literal (c.groupDuration : Word w))
  have ds : t-c.beginTick < 2^w := by omega
  have op := Nat.mod_lt (t-c.beginTick) c.duration_pos
  have cs : c.chunks+1 < 2^w := by have := c.room; omega
  have de : delta.eval p m vs = ((t-c.beginTick : ℕ) : Word w) :=
    eval_diff x _ p m vs t c.beginTick rfl rfl ht hb
  have oe : off.eval p m vs = (c.offset t : Word w) := by
    simp only [off,Term.eval_binary,Term.eval_literal,de,BinaryOp.eval,Fin.val_cast_of_lt ds,Fin.val_cast_of_lt hd]
    rfl
  have minus : (diff off (.literal (c.chunks+1 : ℕ))).eval p m vs =
      ((c.offset t-(c.chunks+1) : ℕ) : Word w) :=
    eval_diff _ _ p m vs _ _ oe rfl (op.trans hd) cs
  fin_cases i
  · change (Term.binary .div delta (.literal (c.groupDuration : Word w))).eval p m vs = (c.group t : Word w)
    simp only [Term.eval_binary,Term.eval_literal,de,BinaryOp.eval,Fin.val_cast_of_lt ds,Fin.val_cast_of_lt hd]
    rfl
  · exact oe
  · change (Term.binary .mul (.binary .mod x (.literal (c.chunks : Word w))) (.literal (a : Word w))).eval p m vs = _
    simp [Term.eval,BinaryOp.eval,x,vs,Fin.val_cast_of_lt ht,
      Fin.val_cast_of_lt (show c.chunks < 2^w by omega), values, Fin.ofNat_eq_cast]
  · change (Term.binary .add (.binary .mul (diff off (.literal (c.chunks+1 : ℕ)))
      (.literal (q : Word w))) (.result 0)).eval p m vs = _
    simp only [Term.eval_binary,Term.eval_literal,minus,BinaryOp.eval]
    simp [Term.eval,values,vs]

end ThreeFlat.RAM.TickClockWords

end OAI

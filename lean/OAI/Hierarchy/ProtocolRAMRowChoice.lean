import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Bounded word selection and row substitution for arithmetic protocol scans -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing
variable {w : ℕ}

def Expr.atRow : Expr → Expr → Expr
  | .row, index => index
  | .lit n, _ => .lit n
  | .lookup b i, index => .lookup b (i.atRow index)
  | .op tag x y, index => .op tag (x.atRow index) (y.atRow index)
  | .branch test x y a b, index =>
    .branch test (x.atRow index) (y.atRow index) (a.atRow index) (b.atRow index)

@[simp] theorem eval_atRow (m : Memory w) (r : Word w) (e index : Expr) :
    (e.atRow index).eval m r = e.eval m (index.eval m r) := by
  induction e <;> simp [Expr.atRow,Expr.eval, *]

def chooseField : (n : ℕ) → ℕ → (Fin n → Expr) → Expr → Expr
  | 0,_,_,_ => .lit 0
  | n+1,base,x,which => .branch .eq which (.lit base) (x 0)
      (chooseField n (base+1) (fun i => x i.succ) which)

theorem eval_chooseField (n base : ℕ) (x : Fin n → Expr) (which : Expr)
    (m : Memory w) (r : Word w) (j : Fin n) (room : base+n ≤ 2^w)
    (index : (which.eval m r).val = base+j.val) :
    (chooseField n base x which).eval m r = (x j).eval m r := by
  induction n generalizing base with
  | zero => exact j.elim0
  | succ n ih =>
    cases j using Fin.cases with
    | zero =>
      have eq : which.eval m r = (base:Word w) := by
        apply Fin.ext
        rw [Fin.val_cast_of_lt (show base<2^w by omega)]
        simpa using index
      simp only [chooseField,Expr.eval,Comparison.test,beq_iff_eq,eq,ite_true]
    | succ j =>
      have diff : which.eval m r ≠ (base:Word w) := by
        intro eq
        have hit := congrArg Fin.val eq
        rw [index,Fin.val_cast_of_lt (show base<2^w by omega)] at hit
        simp at hit
      simp only [chooseField,Expr.eval,Comparison.test,beq_iff_eq,diff,ite_false]
      exact ih (base+1) _ j (by omega) (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using index)

theorem eval_chooseField_outside (n base : ℕ) (x : Fin n → Expr) (which : Expr)
    (m : Memory w) (r : Word w) (room : base+n ≤ 2^w)
    (high : base+n ≤ (which.eval m r).val) :
    (chooseField n base x which).eval m r = 0 := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    have ne : which.eval m r ≠ (base : Word w) := by
      intro eq
      have hit := congrArg Fin.val eq
      rw [Fin.val_cast_of_lt (show base<2^w by omega)] at hit
      omega
    simp only [chooseField,Expr.eval,Comparison.test,beq_iff_eq,ne,ite_false]
    apply ih _ _ (by omega) (by omega)

end Hierarchy.ProtocolRAM

end OAI

import OAI.ThreeFlat.RAM.DescriptorExpr
import Mathlib.Data.ZMod.Defs

namespace OAI
/-! # Native indexed access to a finite public literal table

The table lives in the program's literal instructions. It needs no external
initialization. The straight-line lookup uses exactly three lets per entry
and one default literal.
-/

namespace ThreeFlat.RAM.LiteralTable

open Computability.VPVNP.BurstRAM DescriptorExpr
open scoped Fin.CommRing
variable {w k n : ℕ}

def lookup (a : ℕ → Word w) : ℕ → Term w k 1
  | 0 => .literal 0
  | s+1 => .select .eq (.result 0) (.literal (s : Word w)) (.literal (a s)) (lookup a s)

theorem lookup_binds (a : ℕ → Word w) (s : ℕ) :
    (lookup (k:=k) a s).binds = 3*s+1 := by
  induction s with
  | zero => rfl
  | succ s ih =>
    simp only [lookup, Term.select, Term.binds_letThen, Term.binds_rename, Term.literal, Term.binds, ih]
    omega

theorem lookup_eval (a : ℕ → Word w) (s i : ℕ) (hi : i<s) (hs : s ≤ 2^w)
    (words : Fin k → Word w) (mem : Memory w) (vs : Fin 1 → Word w) (arg : vs 0 = (i : Word w)) :
    (lookup a s).eval words mem vs = a i := by
  induction s with
  | zero => omega
  | succ s ih =>
    have fs : s < 2^w := by omega
    have fi : i < 2^w := by omega
    have eq : ((i : Word w) = (s : Word w)) ↔ i = s := by
      rw [Fin.ext_iff, Fin.val_cast_of_lt fi, Fin.val_cast_of_lt fs]
    simp only [lookup, Term.eval_select, Term.eval, Term.eval_literal, arg, Comparison.test,
      beq_iff_eq, eq]
    split_ifs with h
    · rw [h]
    · exact ih (by omega) (by omega)

/-- Read a locally computed ordinal, evaluating its expression once. -/
def atIndex (a : ℕ → Word w) (s : ℕ) (index : Term w k n) : Term w k n :=
  (lookup a s).instantiate (fun _ => index)

@[simp] theorem atIndex_binds (a : ℕ → Word w) (s : ℕ) (e : Term w k n) :
    (atIndex a s e).binds = 3*s+1+e.binds := by
  simp [atIndex,lookup_binds]

theorem atIndex_eval (a : ℕ → Word w) (s i : ℕ) (hi : i<s) (hs : s≤2^w)
    (words : Fin k → Word w) (mem : Memory w) (vs : Fin n → Word w) (e : Term w k n)
    (index : e.eval words mem vs = (i : Word w)) :
    (atIndex a s e).eval words mem vs = a i := by
  rw [atIndex,Term.eval_instantiate]
  exact lookup_eval _ _ _ hi hs _ _ _ index

/-- Specialize each row function independently. All alternatives share the
same variable environment and one unsigned index register selects its value. -/
def dispatch (i : Fin n) (a : ℕ → Term w k n) : ℕ → Term w k n
  | 0 => .literal 0
  | s+1 => .select .eq (.result i) (.literal (s : Word w)) (a s) (dispatch i a s)

theorem dispatch_binds (i : Fin n) (a : ℕ → Term w k n) (s cap : ℕ)
    (bound : ∀ j<s, (a j).binds ≤ cap) : (dispatch i a s).binds ≤ (cap+2)*s+1 := by
  induction s with
  | zero => simp [dispatch,Term.literal,Term.binds]
  | succ s ih =>
    have h := ih (fun j hj => bound j (Nat.lt_succ_of_lt hj))
    have hs := bound s (Nat.lt_succ_self _)
    simp only [dispatch,Term.select,Term.binds_letThen,Term.binds_rename,Term.literal,
      Term.binds,Nat.mul_succ]
    omega

theorem dispatch_eval (i : Fin n) (a : ℕ → Term w k n) (s x : ℕ) (hx : x<s) (hs : s≤2^w)
    (words : Fin k → Word w) (mem : Memory w) (vs : Fin n → Word w) (arg : vs i = (x : Word w)) :
    (dispatch i a s).eval words mem vs = (a x).eval words mem vs := by
  induction s with
  | zero => omega
  | succ s ih =>
    have eq : ((x : Word w) = (s : Word w)) ↔ x = s := by
      rw [Fin.ext_iff, Fin.val_cast_of_lt (hx.trans_le hs), Fin.val_cast_of_lt (by omega : s<2^w)]
    simp only [dispatch,Term.eval_select,Term.eval,Term.eval_literal,arg,Comparison.test,
      beq_iff_eq,eq]
    split_ifs with h
    · rw [h]
    · exact ih (by omega) (by omega)

end ThreeFlat.RAM.LiteralTable

end OAI

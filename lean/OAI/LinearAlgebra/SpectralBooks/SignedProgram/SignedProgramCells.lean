import Mathlib.Tactic.IntervalCases
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramLocal
import Mathlib.Tactic.DeriveFintype

/-! # Scalar coordinates of a padded program -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram.Hot
open SignedMachine

inductive MoveCell (n : ℕ) where
  | state | inputMove | write (j : Fin n) | direction (j : Fin n)
  deriving DecidableEq, Fintype

inductive RowCell (n : ℕ) where
  | state | input | read (j : Fin n) | kind | out | move (b : Bool) (c : MoveCell n)
  deriving DecidableEq, Fintype

inductive Cell (n : ℕ) where
  | tapes | rows | row (i : Fin n) (c : RowCell n)
  deriving DecidableEq, Fintype

def MoveCell.value {n : ℕ} (m : Move n) : MoveCell n → ℕ
  | .state => m.state.val
  | .inputMove => directionCode m.inputMove
  | .write j => symbolCode (m.work j).1
  | .direction j => directionCode (m.work j).2

def RowCell.value {n : ℕ} (r : Row n) : RowCell n → ℕ
  | .state => r.state.val
  | .input => symbolCode r.input
  | .read j => symbolCode (r.reads j)
  | .kind => r.kind.val
  | .out => outputCode r.out
  | .move b c => c.value (r.next b)

def Cell.value {n : ℕ} (t : Table n) : Cell n → ℕ
  | .tapes => t.tapes.val
  | .rows => t.rows.val
  | .row i c => c.value (t.row i)

def MoveCell.arity {n : ℕ} : MoveCell n → ℕ
  | .state => n+1 | _ => 3

def RowCell.arity {n : ℕ} : RowCell n → ℕ
  | .state => n+1 | .move _ c => c.arity | _ => 3

def Cell.arity {n : ℕ} : Cell n → ℕ
  | .row _ c => c.arity | _ => n+1

private def sym (a : ℕ) := if a = 0 then Symbol.blank else if a = 1 then .zero else .one
private def dir (a : ℕ) := if a = 0 then Direction.left else if a = 1 then .stay else .right
private def out (a : ℕ) := if a = 0 then Output.zero else if a = 1 then .pos else .neg

@[simp] private theorem sym_val (s : Symbol) : sym (symbolCode s) = s := by cases s <;> decide
@[simp] private theorem dir_val (d : Direction) : dir (directionCode d) = d := by cases d <;> decide
@[simp] private theorem out_val (o : Output) : out (outputCode o) = o := by cases o <;> decide

private def reconstructMove (n : ℕ) (f : MoveCell n → ℕ) : Move n :=
  ⟨bounded n (f .state),dir (f .inputMove),fun i ↦ (sym (f (.write i)),dir (f (.direction i)))⟩

private def reconstructRow (n : ℕ) (f : RowCell n → ℕ) : Row n :=
  ⟨bounded n (f .state), sym (f .input), fun i ↦ sym (f (.read i)), bounded 2 (f .kind),
   out (f .out), fun b ↦ reconstructMove n (fun c ↦ f (.move b c))⟩

def reconstruct (n : ℕ) (f : Cell n → ℕ) : Table n :=
  ⟨bounded n (f .tapes),bounded n (f .rows),fun i ↦ reconstructRow n (fun c ↦ f (.row i c))⟩

@[simp] private theorem bounded_self {n : ℕ} (v : Fin (n+1)) : bounded n v.val = v :=
  Fin.ext (Nat.min_eq_right (Nat.le_of_lt_succ v.isLt))

private theorem reconstructMove_value {n : ℕ} (m : Move n) :
    reconstructMove n (MoveCell.value m) = m := by
  cases m; simp [reconstructMove,MoveCell.value]

private theorem reconstructRow_value {n : ℕ} (r : Row n) :
    reconstructRow n (RowCell.value r) = r := by
  cases r; simp [reconstructRow,RowCell.value,reconstructMove_value]

theorem reconstruct_value {n : ℕ} (t : Table n) : reconstruct n (Cell.value t) = t := by
  cases t; simp [reconstruct,Cell.value,reconstructRow_value]

private theorem sym_lt (s : Symbol) : symbolCode s < 3 := by cases s <;> decide
private theorem dir_lt (s : Direction) : directionCode s < 3 := by cases s <;> decide
private theorem out_lt (s : Output) : outputCode s < 3 := by cases s <;> decide

theorem Cell.value_lt {n : ℕ} (t : Table n) (c : Cell n) : c.value t < c.arity := by
  cases c with
  | tapes => exact t.tapes.isLt
  | rows => exact t.rows.isLt
  | row i c =>
    cases c with
    | state => exact (t.row i).state.isLt
    | read j => exact sym_lt _
    | input => exact sym_lt _
    | out => exact out_lt _
    | kind => exact (t.row i).kind.isLt
    | move b c =>
      cases c with
      | state => exact ((t.row i).next b).state.isLt
      | inputMove => exact dir_lt _
      | write j => exact sym_lt _
      | direction j => exact dir_lt _

theorem Cell.arity_bound {n : ℕ} (c : Cell n) : c.arity ≤ n+3 := by
  cases c with
  | row i r =>
    cases r with
    | move b m => cases m <;> simp [Cell.arity,RowCell.arity,MoveCell.arity]
    | _ => simp [Cell.arity,RowCell.arity]
  | _ => simp [Cell.arity]

private theorem code_sym {v : ℕ} (h : v < 3) : symbolCode (sym v) = v := by interval_cases v <;> decide
private theorem code_dir {v : ℕ} (h : v < 3) : directionCode (dir v) = v := by interval_cases v <;> decide
private theorem code_out {v : ℕ} (h : v < 3) : outputCode (out v) = v := by interval_cases v <;> decide

theorem value_reconstruct {n : ℕ} (f : Cell n → ℕ) (h : ∀ c, f c < c.arity) (c : Cell n) :
    c.value (reconstruct n f) = f c := by
  have ht := h c
  cases c with
  | tapes => exact Nat.min_eq_right (Nat.le_of_lt_succ ht)
  | rows => exact Nat.min_eq_right (Nat.le_of_lt_succ ht)
  | row i c =>
    cases c with
    | state | kind => exact Nat.min_eq_right (Nat.le_of_lt_succ ht)
    | read j => exact code_sym ht
    | input => exact code_sym ht
    | out => exact code_out ht
    | move b c =>
      cases c with
      | state => exact Nat.min_eq_right (Nat.le_of_lt_succ ht)
      | inputMove | direction j => exact code_dir ht
      | write j => exact code_sym ht

end SignedProgram.Hot

end SpectralBooks
end LinearAlgebra
end OAI

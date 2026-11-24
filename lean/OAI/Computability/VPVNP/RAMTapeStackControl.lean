import OAI.Computability.VPVNP.RAMTapeRun
import OAI.Computability.VPVNP.RAMTapeStacks
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum

/-!
# Two physical tapes for a fixed finite bank of bit stacks

The first tape lists the stacks in order, each terminated by a blank.
To reach stack `i`, move the preceding symbols onto the second tape. Each
saved symbol gets a nonblank tag, so a stored delimiter is distinguishable
from the empty scratch tape. A push or pop takes place at the exposed top.
Then restore the saved prefix, clearing every scratch cell as it is consumed.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.StackCompiler

open UniversalMachine

/-- Control states used to scan to one stack and restore the packed tape. -/
inductive Phase (k : ℕ) (Q : Type*) where
  | ready (q : Q)
  | seek (q : Q) (remaining : Fin (k+1))
  | stash (q : Q) (remaining : Fin (k+1)) (value : Symbol)
  | tag (q : Q) (remaining : Fin (k+1))
  | pushing (q : Q) (bit : Bool)
  | restore (q : Q)
  | value (q : Q)
  | write (q : Q) (value : Symbol)
  deriving Fintype

/-- Encode a Boolean by one of the two nonblank tape symbols. -/
def bit (b : Bool) : Symbol := if b then 2 else 1

variable {k : ℕ} {Q : Type*}

/-- Number of further stack separators to cross after reading this symbol. -/
def remaining (i : Fin (k+1)) (x : Symbol) : Fin (k+1) :=
  if x = 0 then ⟨i.val-1, by omega⟩ else i

/-- The physical two-tape instructions implementing the given stack table. -/
def rows (code : StackCode (Fin k) Q) : Control (Phase k Q)
  | .ready q, x, y =>
    match code q with
    | .push i .. | .pop i .. => .one (.next (.seek q i.castSucc) x 0 y 0)
    | .goto q' => .one (.next (.ready q') x 0 y 0)
    | .choose low high => .two (.next (.ready low) x 0 y 0) (.next (.ready high) x 0 y 0)
    | .halt b => .one (.halt b)
  | .seek q i, x, y =>
    if i.val = 0 then match code q with
      | .push _ b q' => .one (.next (.pushing q' b) x 1 y 0)
      | .pop _ f => if x = 0 then .one (.next (.restore (f none)) x 0 y 0)
        else .one (.next (.restore (f (some (x = 2)))) 0 2 y 0)
      | _ => .stop
    else .one (.next (.stash q (remaining i x) x) 0 2 y 1)
  | .stash q i x, a, _ => .one (.next (.tag q i) a 0 x 1)
  | .tag q i, x, _ => .one (.next (.seek q i) x 0 2 0)
  | .pushing q b, _, y => .one (.next (.restore q) (bit b) 0 y 0)
  | .restore q, x, y => if y = 0 then .one (.next (.ready q) x 0 y 0)
      else .one (.next (.value q) x 0 0 2)
  | .value q, x, y => .one (.next (.write q y) x 1 0 2)
  | .write q x, _, y => .one (.next (.restore q) x 0 y 0)

/-- Store the nearest saved symbol first. -/
def scratch (saved : List Symbol) : List Symbol :=
  saved.flatMap fun x => [2, x]

variable (code : StackCode (Fin k) Q)

theorem restore_run (q : Q) (saved data : List Symbol) :
    Runs (rows code) (3 * saved.length + 1) (.restore q) (tapeList data)
      (tapeList (scratch saved)) (.ready q) (tapeList (saved.reverse ++ data)) (tapeList []) := by
  induction saved generalizing data with
  | nil =>
    change Runs (rows code) 1 (.restore q) (tapeList data) (tapeList []) (.ready q) (tapeList data) (tapeList [])
    apply Runs.cons rfl
    rw [update_stay]
    exact .nil ..
  | cons x xs ih =>
    have h := ih (x :: data)
    simp only [scratch, List.flatMap_cons, List.cons_append, List.nil_append,
      List.reverse_cons, List.append_assoc, List.length_cons, Nat.mul_succ] at *
    rw [show 3 * xs.length + 3 + 1 = ((3 * xs.length + 1 + 1) + 1) + 1 by omega]
    apply Runs.cons rfl
    simp only [update_stay, pop_cell]
    apply Runs.cons rfl
    simp only [left_for_push, pop_cell]
    apply Runs.cons rfl
    simpa only [replace_top, update_stay, cells_head] using h

/-- The byte stream of a block of consecutive stacks. -/
def fields (ss : List (List Bool)) : List Symbol :=
  ss.flatMap fun s => s.map bit ++ [0]

@[simp] theorem fields_cons (s : List Bool) (ss : List (List Bool)) :
    fields (s :: ss) = s.map bit ++ 0 :: fields ss := by simp [fields, List.append_assoc]

end RAMTape.StackCompiler

end VPVNP
end Computability
end OAI

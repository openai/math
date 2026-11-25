import OAI.ThreeFlat.RAM.ChunkRequestCursor
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace OAI
/-! # Natural addresses of the prepared request words -/

namespace ThreeFlat.RAM.ChunkRequests

open Computability.VPVNP.BurstRAM PrivateRAM

variable {w : ℕ}

def Request.column (r : Request w) : Fin 4 → Word w := ![r.chunk,r.mode,r.offset,r.expected]

private theorem eq_of_columns {x y : Request w} (h : ∀ j, x.column j = y.column j) : x = y := by
  cases x
  cases y
  congr 1
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3

theorem readRow_column (m : Memory w) (cursor : Word w) (fit : cursor.val+3 < 2^w) (j : Fin 4) :
    (readRow m cursor).column j = m (cursor.val+j.val) := by
  have h₁ : (1:Word w).val = 1 := Nat.mod_eq_of_lt (show (1:ℕ) < 2^w by omega)
  have h₂ : (2:Word w).val = 2 := Nat.mod_eq_of_lt (show (2:ℕ) < 2^w by omega)
  have h₃ : (3:Word w).val = 3 := Nat.mod_eq_of_lt (show (3:ℕ) < 2^w by omega)
  fin_cases j <;> simp [Request.column,readRow,Fin.val_add,Nat.mod_eq_of_lt fit,
    Nat.mod_eq_of_lt (show cursor.val+1 < 2^w by omega),
    Nat.mod_eq_of_lt (show cursor.val+2 < 2^w by omega)]

/-- A contiguous word layout suffices for all the ordered-record preparation
premises of the native machine. -/
theorem preparedRows_eq_of_columns (m : Memory w) (cursor stride : Word w) (n : ℕ)
    (pitch : stride.val = 4) (fit : cursor.val+n*4 ≤ 2^w) (rows : Fin n → Request w)
    (read : ∀ (i : Fin n) (j : Fin 4), m (cursor.val+i.val*4+j.val) = (rows i).column j) :
    preparedRows m cursor stride n = List.ofFn rows := by
  apply congrArg List.ofFn
  funext i
  apply eq_of_columns
  intro j
  have hi := i.isLt
  have curr : (cursorAt stride i.val cursor).val = cursor.val+i.val*4 := by
    simpa only [pitch] using cursorAt_val stride cursor i.val (by rw [pitch]; omega)
  rw [readRow_column m _ (by rw [curr]; omega),curr]
  exact read i j

end ThreeFlat.RAM.ChunkRequests

end OAI

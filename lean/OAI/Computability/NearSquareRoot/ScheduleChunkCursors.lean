import OAI.Computability.IntegerMultiplication.Code.Padding
import Mathlib.Tactic

/-! # Uniform row and column cursors for fenced products -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkCursor

open IntegerMultiplication.Code

/-- Each axis stores its remaining digit count and its current bit offset.
The descriptor also stores the width of a digit and the number of digits. -/
abbrev Cursor := (Tally × Tally) × (Tally × Tally) × Tally × Tally

def atPair (r u i j : ℕ) : Cursor :=
  ((tally (r-i), tally (i*u)), (tally (r-j), tally (j*u)), tally u, tally r)

def initial (p : Tally × Tally) : Cursor :=
  ((p.2, []), (p.2, []), p.1, p.2)

theorem easy_initial : Easy initial := by unfold initial; fun_prop

theorem initial_eq (r u : ℕ) : initial (tally u,tally r) = atPair r u 0 0 := by
  simp [initial, atPair, tally]

private theorem easy_tail : Easy (fun l : Tally => l.tail) := by
  convert Easy.listCase [] (Easy.snd (X := Unit) (Y := Tally)) using 1
  funext l
  cases l <;> rfl

private theorem easy_empty : Easy (fun l : Tally => l.isEmpty) := by
  convert Easy.listCase true (Easy.const false (X := Unit × Tally)) using 1
  funext l
  cases l <;> rfl

def columnStep (c : Cursor) : Cursor :=
  (c.1, (c.2.1.1.tail,c.2.1.2 ++ c.2.2.1), c.2.2)

def rowStep (c : Cursor) : Cursor :=
  ((c.1.1.tail,c.1.2 ++ c.2.2.1), (c.2.2.2,[]), c.2.2)

/-- The two end tests are ordinary inspections of runtime unary data. -/
def advance (c : Cursor) : Cursor :=
  bif c.2.1.1.tail.isEmpty then rowStep c else columnStep c

def exhausted (c : Cursor) := c.1.1.isEmpty

theorem easy_exhausted : Easy exhausted := by
  exact (show Easy (fun c : Cursor => c.1.1) by fun_prop).compose easy_empty

theorem easy_advance : Easy advance := by
  have h₁ : Easy rowStep := by
    unfold rowStep
    exact (((show Easy (fun c : Cursor => c.1.1) by fun_prop).compose easy_tail).pair
      (by fun_prop)).pair (by fun_prop)
  have h₂ : Easy columnStep := by
    unfold columnStep
    exact Easy.fst.pair ((((show Easy (fun c : Cursor => c.2.1.1) by fun_prop).compose easy_tail).pair
      (by fun_prop)).pair (by fun_prop))
  exact ((((show Easy (fun c : Cursor => c.2.1.1) by fun_prop).compose easy_tail).compose
    easy_empty).pair Easy.identity).compose (Easy.ifst h₂ h₁)

private theorem tail_tally (v : ℕ) : (tally v).tail = tally (v-1) := by
  cases v <;> simp [tally]

private theorem append_tally (m n : ℕ) : tally m ++ tally n = tally (m+n) := by
  rw [← recover_tally (tally m ++ tally n)]
  simp

theorem advance_column {r j : ℕ} (u i : ℕ) (hj : j+1 < r) :
    advance (atPair r u i j) = atPair r u i (j+1) := by
  have he : (tally (r-(j+1))).isEmpty = false := by
    cases h : r-(j+1) with
    | zero => omega
    | succ k => simp
  simp only [advance, atPair, tail_tally, he, Bool.cond_false, columnStep, append_tally, Nat.succ_mul,
    show r-j-1 = r-(j+1) by omega]

theorem advance_row {r j : ℕ} (u i : ℕ) (hj : j+1 = r) :
    advance (atPair r u i j) = atPair r u (i+1) 0 := by
  simp [advance, atPair, tail_tally, show r-j-1=0 by omega, show tally 0 = [] from rfl,
    rowStep, append_tally, Nat.succ_mul, show r-i-1=r-(i+1) by omega]

theorem exhausted_iff (r u i j : ℕ) : exhausted (atPair r u i j) = true ↔ r ≤ i := by
  simp [exhausted, atPair, tally, Nat.sub_eq_zero_iff_le]

theorem advance_to_column (r u i j : ℕ) (hj : j < r) :
    advance^[j] (atPair r u i 0) = atPair r u i j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (by omega), advance_column _ _ hj]

theorem advance_one_row {r : ℕ} (hr : 0 < r) (u i : ℕ) :
    advance^[r] (atPair r u i 0) = atPair r u (i+1) 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  rw [Function.iterate_succ_apply', advance_to_column _ _ _ _ (by omega), advance_row _ _ rfl]

/-- Slot `i*r+j` addresses exactly the pair `(i,j)` in row-major order. -/
theorem visit {r : ℕ} (hr : 0 < r) (u i j : ℕ) (hj : j < r) :
    advance^[i*r+j] (atPair r u 0 0) = atPair r u i j := by
  have rows (l : ℕ) : advance^[l*r] (atPair r u 0 0) = atPair r u l 0 := by
    induction l with
    | zero => simp
    | succ l ih =>
      rw [Nat.succ_mul, Nat.add_comm, Function.iterate_add_apply, ih, advance_one_row hr]
  rw [Nat.add_comm, Function.iterate_add_apply, rows, advance_to_column _ _ _ _ hj]

/-- At most a linear amount of cursor data is live even when the number of
digit products is quadratic in the input length. -/
theorem size_atPair {r u i j n : ℕ} (hi : i ≤ r) (hj : j ≤ r) (hr : r ≤ n)
    (hu : u ≤ n) (hru : r*u ≤ 2*n) :
    size (atPair r u i j) ≤ 16*n+11 := by
  have h₁ := (Nat.mul_le_mul_right u hi).trans hru
  have h₂ := (Nat.mul_le_mul_right u hj).trans hru
  simp [atPair, size_tally]
  omega

end ChunkCursor

end NearSquareRoot
end Computability
end OAI

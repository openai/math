import OAI.LinearAlgebra.SpectralBooks.SignedMachine.SignedTableauExecution
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramTable

/-! # Finite rows of the signed computation tableau

A row with `r` steps remaining records a radius-`r` window about each
head. The next row reads only positions present in the previous one.
A transitioned work tape writes at the old head before it moves.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram

open SignedMachine

abbrev Cell (r : ℕ) := Fin (2*r+1)

/-- Position relative to the head in a row of radius `r`. -/
def Cell.position {r : ℕ} (i : Cell r) : ℤ := (i.val : ℤ) - r

def Cell.center (r : ℕ) : Cell r := ⟨r, by omega⟩

@[simp] theorem Cell.position_center (r : ℕ) : (Cell.center r).position = 0 := by
  simp [Cell.center, Cell.position]

/-- Static wire address for a cell of the next (narrower) tape row. -/
def Cell.previous {r : ℕ} (d : Direction) (i : Cell r) : Cell (r+1) :=
  match d with
  | .left => ⟨i.val, by omega⟩
  | .stay => ⟨i.val+1, by omega⟩
  | .right => ⟨i.val+2, by omega⟩

@[simp] theorem Cell.position_previous {r : ℕ} (d : Direction) (i : Cell r) :
    (Cell.previous d i).position = i.position + d.offset := by
  cases d <;> simp [Cell.previous, Cell.position, Direction.offset] <;> omega

/-- A bounded window on the original two-sided tape. -/
def window {r : ℕ} (t : Tape) (i : Cell r) : Symbol := t.atCell i.position

@[simp] theorem window_center (t : Tape) (r : ℕ) : window t (Cell.center r) = t.head := by
  simp [window]

theorem window_move {r : ℕ} (t : Tape) (d : Direction) (i : Cell r) :
    window (t.move d) i = window t (Cell.previous d i) := by
  simp [window, Tape.atCell_move]

theorem window_writeMove {r : ℕ} (t : Tape) (s : Symbol) (d : Direction) (i : Cell r) :
    window (t.writeMove (s,d)) i =
      if (Cell.previous d i).position = 0 then s else window t (Cell.previous d i) := by
  simp [window, Tape.atCell_writeMove]

/-- The unary input at relative column `z` is a statically addressed bit,
or a blank outside the supplied input. -/
def initialSymbol {n : ℕ} (x : Fin n → Bool) (z : ℤ) : Symbol :=
  if hz : 0 ≤ z ∧ z.toNat < n then (if x ⟨z.toNat,hz.2⟩ then .one else .zero) else .blank

theorem initialSymbol_eq {n : ℕ} (p : Program) (x : Fin n → Bool) (z : ℤ) :
    ((p.initial (List.ofFn x)).inputTape).atCell z = initialSymbol x z := by
  cases z with
  | ofNat k =>
    cases k with
    | zero =>
      cases n with
      | zero => simp [Program.initial, Tape.atCell, initialSymbol]
      | succ n => simp [Program.initial, Tape.atCell, initialSymbol, List.ofFn_succ]
    | succ k =>
      by_cases hk : k+1 < n
      · simp [Program.initial, Tape.atCell, initialSymbol, hk, show ¬ ((k : ℤ)+1 < 0) by omega]
      · simp [Program.initial, Tape.atCell, initialSymbol, hk]
  | negSucc k => simp [Program.initial, Tape.atCell, initialSymbol]

/-- Those cells of a live or halted configuration which can still affect its output. -/
@[ext] structure Frame (n r : ℕ) where
  control : Output ⊕ ℕ
  cells : Option (Fin n) → Cell r → Symbol

def Frame.halted (n r : ℕ) (o : Output) : Frame n r :=
  ⟨.inl o, fun _ _ => .blank⟩

def Frame.ofConfig {n r : ℕ} (c : Config) : Frame n r :=
  ⟨.inr c.state, fun tape i =>
    match tape with
    | none => window c.inputTape i
    | some j => window (c.work.getD j.val Tape.blank) i⟩

def Frame.ofState {n r : ℕ} : Output ⊕ Config → Frame n r :=
  Sum.elim (Frame.halted n r) Frame.ofConfig

def Frame.initial {n r : ℕ} (x : Fin n → Bool) : Frame n r :=
  ⟨.inr 0, fun tape i => match tape with
    | none => initialSymbol x i.position
    | some _ => .blank⟩

@[simp] private theorem blank_atCell (z : ℤ) : Tape.blank.atCell z = .blank := by
  cases z with
  | ofNat k => cases k <;> rfl
  | negSucc k => rfl

theorem Frame.initial_eq {n r : ℕ} (p : Program) (x : Fin n → Bool) :
    Frame.initial (r := r) x = Frame.ofConfig (p.initial (List.ofFn x)) := by
  refine Frame.ext ?_ ?_
  · rfl
  funext t i
  cases t with
  | none => exact (initialSymbol_eq p x _).symm
  | some j =>
    by_cases hj : j.val < p.workTapes <;> simp [Frame.initial, Frame.ofConfig, Program.initial,
      List.getD, List.getElem?_replicate, hj, window]

/-- The successor row, given the instruction's read-only move and work-tape writes. -/
def Frame.advance {n r : ℕ} (f : Frame n (r+1)) (tr : Transition) : Frame n r where
  control := .inr tr.state
  cells tape i := match tape with
    | none => f.cells none (Cell.previous tr.inputMove i)
    | some j => match tr.workMoves[j.val]? with
      | none => .blank
      | some (s,d) => if (Cell.previous d i).position = 0 then s
        else f.cells (some j) (Cell.previous d i)

/-- The next row of the finite tableau agrees cellwise with a machine transition. -/
theorem Frame.advance_eq {n r : ℕ} {c c' : Config} {tr : Transition}
    (h : c.advance tr = some c') :
    (Frame.ofConfig (n := n) (r := r+1) c).advance tr = Frame.ofConfig c' := by
  unfold Config.advance at h
  split at h
  next hlen =>
    cases h
    refine Frame.ext ?_ ?_
    · rfl
    funext t i
    cases t with
    | none => exact (window_move ..).symm
    | some j =>
      by_cases hj : j.val < tr.workMoves.length
      · have hjc : j.val < c.work.length := by omega
        simp [Frame.ofConfig, Frame.advance, List.getD, hjc, hlen]
        exact (by simpa using (window_writeMove (c.work[j.val]) (tr.workMoves[j.val].1)
          (tr.workMoves[j.val].2) i).symm)
      · have hjc : ¬ j.val < c.work.length := by omega
        simp [Frame.ofConfig, Frame.advance, List.getD, hjc, hlen, window]
  next => contradiction

end SignedProgram

end SpectralBooks
end LinearAlgebra
end OAI

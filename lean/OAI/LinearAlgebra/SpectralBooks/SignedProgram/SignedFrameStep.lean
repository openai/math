import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedTapeWindow

/-! # Correctness of a bounded tape-window computation

The lookup reads just the central symbol of each active tape. Its selected
action, the next guess bit and a three-column stencil determine the next row.
The projected configuration agrees with the actual signed machine at every
tick of the original clock.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram

open SignedMachine

def Frame.lookup {n r : ℕ} (t : Table n) (f : Frame n r) (state : ℕ) : Option Rule :=
  t.program.table.find? fun row =>
    row.state == state && row.inputSymbol == f.cells none (Cell.center r) &&
    row.workSymbols == activeList t.tapes (fun j => f.cells (some j) (Cell.center r))

theorem active_heads {n r : ℕ} (t : Table n) (c : Config) (hc : c.work.length = t.tapes.val) :
    activeList t.tapes (fun j => (Frame.ofConfig (n := n) (r := r) c).cells (some j) (Cell.center r)) =
      c.work.map Tape.head := by
  apply List.ext_getElem
  · simp [activeList, hc]
  · intro j hj hk
    have h : j < c.work.length := by simpa using hk
    simp [activeList, Frame.ofConfig, List.getD, List.getElem?_eq_getElem h]

/-- Interpreting the selected action on the new row, including failure and
the forced zero bit for a deterministic tick. -/
def Frame.applyAction {n r : ℕ} (f : Frame n (r+1)) (bit : Bool) : Option Action → Frame n r
  | none => Frame.halted n r .zero
  | some (.halt o) => Frame.halted n r (if bit then .zero else o)
  | some (.step tr) => if bit then Frame.halted n r .zero else f.advance tr
  | some (.branch a b) => f.advance (if bit then b else a)

def Frame.tick {n r : ℕ} (t : Table n) (bit : Bool) (f : Frame n (r+1)) : Frame n r :=
  match f.control with
  | .inl o => Frame.halted _ _ (if bit then .zero else o)
  | .inr q => f.applyAction bit ((f.lookup t q).map Rule.action)

private theorem table_actionArity {n : ℕ} (t : Table n) (a : Action)
    (ha : ∃ row ∈ t.program.table, row.action = a) : ProgramCode.ActionArity t.tapes.val a := by
  obtain ⟨row, hr, rfl⟩ := ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  dsimp only [Row.rule]
  unfold Row.action
  split
  · trivial
  · split <;> simp [ProgramCode.ActionArity, Move.transition, activeList]

/-- The number of work tapes stays equal to the arity stored in the table. -/
def validState {n : ℕ} (t : Table n) : Output ⊕ Config → Prop :=
  Sum.elim (fun _ => True) (fun c => c.work.length = t.tapes.val)

private theorem advance_exists {n : ℕ} (t : Table n) {tr : Transition} {c : Config}
    (hc : c.work.length = t.tapes.val) (ht : tr.workMoves.length = t.tapes.val) :
    ∃ c', c.advance tr = some c' ∧ c'.work.length = t.tapes.val := by
  simp [Config.advance, hc, ht]

/-- A tick on finite windows agrees with one step of the original machine,
and the successor retains the tape arity invariant. -/
theorem Frame.tick_correct {n r : ℕ} (t : Table n) (bit : Bool) (u : Output ⊕ Config)
    (hu : validState t u) :
    (Frame.ofState (n := n) (r := r+1) u).tick t bit =
        Frame.ofState (tableauStep t.program.next bit u) ∧
      validState t (tableauStep t.program.next bit u) := by
  rcases u with o | c
  · exact ⟨rfl, trivial⟩
  change c.work.length = t.tapes.val at hu
  let pred (row : Rule) := row.state == c.state && row.inputSymbol == c.inputTape.head &&
    row.workSymbols == c.work.map Tape.head
  have he : (Frame.ofConfig (n := n) (r := r+1) c).lookup t c.state = t.program.table.find? pred := by
    simp [Frame.lookup, Frame.ofConfig, pred, ← active_heads (r := r+1) t c hu]
  change (Frame.ofConfig c).applyAction bit (((Frame.ofConfig c).lookup t c.state).map Rule.action) = _ ∧ _
  rw [he]
  simp only [tableauStep, Program.next]
  have hp : (fun row : Rule => row.state == c.state && row.inputSymbol == c.inputTape.head &&
      row.workSymbols == c.work.map Tape.head) = pred := rfl
  rw [hp]
  cases h : t.program.table.find? pred with
  | none => exact ⟨rfl, trivial⟩
  | some row =>
    have ha := table_actionArity t row.action ⟨row, List.mem_of_find?_eq_some h, rfl⟩
    cases hr : row.action with
    | halt o =>
      simp [hr, Frame.applyAction, Frame.ofState, validState]
    | step tr =>
      obtain ⟨c', hc', hn⟩ := advance_exists t hu (hr ▸ ha)
      cases bit <;> simp [hr, hc', Frame.applyAction, Frame.ofState, validState, hn,
        Frame.advance_eq hc']
    | branch a b =>
      rw [hr] at ha
      obtain ⟨ca, hca, hna⟩ := advance_exists t hu ha.1
      obtain ⟨cb, hcb, hnb⟩ := advance_exists t hu ha.2
      cases bit <;> simp [hr, hca, hcb, Frame.applyAction, Frame.ofState, validState,
        hna, hnb, Frame.advance_eq hca, Frame.advance_eq hcb]

end SignedProgram

end SpectralBooks
end LinearAlgebra
end OAI

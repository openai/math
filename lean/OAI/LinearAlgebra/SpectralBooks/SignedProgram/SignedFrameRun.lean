import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedFrameStep
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramLookupSpec

/-! # Signed path counts from bounded computation rows

For each fixed bit string, projecting an actual machine run onto tape windows
commutes with every tick. Summing the final signed outputs after exactly the
universal clock length gives the prescribed integer coefficient.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram

open SignedMachine

/-- Only states named by the program or a halting output are reachable. -/
def Frame.bounded {n r : ℕ} (f : Frame n r) : Prop := f.control.elim (fun _ => True) (· ≤ n)

theorem Frame.bounded_initial {n r : ℕ} (x : Fin n → Bool) : (Frame.initial (r := r) x).bounded :=
  Nat.zero_le _

theorem Frame.bounded_tick {n r : ℕ} (t : Table n) (bit : Bool) (f : Frame n (r+1)) :
    (f.tick t bit).bounded := by
  unfold Frame.tick
  split
  · trivial
  next q _ =>
    cases h : f.lookup t q with
    | none => trivial
    | some row =>
      have hr : row ∈ t.program.table := List.mem_of_find?_eq_some h
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
      dsimp only [Row.rule, Option.map_some]
      unfold Row.action
      split
      · trivial
      · split
        · cases bit <;> simp [Frame.applyAction, Frame.bounded, Frame.advance, Frame.halted,
            Move.transition]
          exact Nat.le_of_lt_succ (Fin.isLt _)
        · cases bit <;> simp [Frame.applyAction, Frame.bounded, Frame.advance, Move.transition] <;>
            exact Nat.le_of_lt_succ (Fin.isLt _)

/-- All `r` guesses are assigned in chronological order on the decreasing windows. -/
def Frame.run {n : ℕ} (t : Table n) :
    (r : ℕ) → (Fin r → Bool) → Frame n r → Frame n 0
  | 0, _, f => f
  | r+1, b, f => Frame.run t r (Fin.tail b) (f.tick t (b 0))

def Frame.output {n r : ℕ} (f : Frame n r) : Output := f.control.elim id fun _ => .zero

/-- Reading the final row gives precisely the output of the complete machine run. -/
theorem Frame.run_correct {n : ℕ} (t : Table n) (r : ℕ) (b : Fin r → Bool)
    (u : Output ⊕ Config) (hu : validState t u) :
    (Frame.run t r b (Frame.ofState u)).output = tableauOutput t.program.next r b u := by
  induction r generalizing u with
  | zero => cases u <;> rfl
  | succ r ih =>
    obtain ⟨hs,hv⟩ := Frame.tick_correct (r := r) t (b 0) u hu
    rw [Frame.run, hs, tableauOutput, ih _ _ hv]

/-- The sum over a parsed table's executions is the signed coefficient of the
actual witness polynomial at this input. -/
theorem sum_run_eq_signedWitness {n : ℕ} (t : Table n) (x : Fin n → Bool)
    (h : ProgramCode.decode (List.ofFn x) = some t.program) :
    (∑ b : Fin (n^100) → Bool,
      (Frame.run t (n^100) b (Frame.initial x)).output.value) = signedWitness x := by
  let u : Output ⊕ Config := .inr (t.program.initial (List.ofFn x))
  have hu : validState t u := by simp [u, validState, Program.initial, Table.program]
  have hit (b : Fin (n^100) → Bool) : (Frame.run t (n^100) b (Frame.initial x)).output =
      tableauOutput t.program.next (n^100) b u := by
    rw [Frame.initial_eq t.program x]
    exact Frame.run_correct t _ b u hu
  simp only [hit, sum_tableauOutput, u, Sum.elim_inr, signedWitness, h]
  rfl

end SignedProgram

end SpectralBooks
end LinearAlgebra
end OAI

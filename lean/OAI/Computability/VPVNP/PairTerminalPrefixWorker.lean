import OAI.Computability.VPVNP.PairTerminalPrefix
import OAI.Computability.VPVNP.PairSimulationTerminalLink

/-!
# Live terminal-prefix instruction table

The terminal header is recovered from the workspace and size exponent in the
eleven public operands. Every active call takes its width and prefix table
heads from that header, advances one arc, and returns the successor ordinal.
The closing call publishes the role-table displacement and accepts.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalPrefix.Worker

open BurstRAM BurstRAM.PrivateRAM CompressorRecords
open scoped Fin.CommRing

variable {w : ℕ}

/-- Terminal header at the high end of the pair workspace. -/
abbrev header (pub : Fin 11 → Word w) : Word w := TerminalLink.header pub

/-- Width-array head, prefix-array head, and running-total address loaded from the terminal
header for the prefix worker. -/
def data (pub : Fin 11 → Word w) (m : Memory w) : Fin 3 → Word w :=
  let h := header pub
  ![m (h + 9).val, m (h + 11).val, h + 12]

/-- The 41 native instructions that recover the terminal header, process one arc's width, or
publish the closing displacement. -/
def instruction (w : ℕ) : Fin 41 → Instr w 41 7 11 :=
  ![.publicWord 1 7 1, .constant 2 1 2, .binary .shiftLeft 1 2 1 3, .binary .mul 1 1 1 4,
    .publicWord 3 2 5, .binary .add 1 3 1 6, .constant 3 32 7, .binary .sub 1 1 3 8,
    .stateWord 0 9, .constant 3 8 10, .binary .add 3 1 3 11, .readExternal 3 3 12,
    .jumpEq 0 3 30 13,
    .constant 3 9 14, .binary .add 3 1 3 15, .readExternal 3 3 16, .binary .add 3 3 0 17,
    .readExternal 3 3 18, .constant 4 11 19, .binary .add 4 1 4 20, .readExternal 4 4 21,
    .binary .add 4 4 0 22, .constant 5 12 23, .binary .add 5 1 5 24, .readExternal 6 5 25,
    .writeExternal 4 6 26, .binary .add 6 6 3 27, .writeExternal 5 6 28, .binary .add 0 0 2 29,
    .returnState 0,
    .constant 3 5 31, .binary .add 3 1 3 32, .readExternal 3 3 33, .constant 4 12 34,
    .binary .add 4 1 4 35, .readExternal 4 4 36, .binary .add 3 3 4 37, .constant 4 14 38,
    .binary .add 4 1 4 39, .writeExternal 4 3 40, .accept]

/-- Resizable terminal prefix worker table, assembled at six-bit word width with entry at
instruction zero. -/
def table : Template 41 7 11 := ⟨6, 0, instruction 6⟩

set_option maxRecDepth 4096 in
theorem resize_instruction (w : ℕ) (pc : Fin 41) :
    (instruction 6 pc).resize w = instruction w pc := by fin_cases pc <;> rfl

private def read (m : Memory w) (addr : Word w) := Event.read addr (m addr.val)

private def pre (pub : Fin 11 → Word w) (m : Memory w) : List (Event w) :=
  List.replicate 11 .tick ++ [read m (header pub + 8), .tick]

/-- Report for arc ordinal i. It writes the current total into that arc's prefix cell, adds the
arc width, and returns the next ordinal. -/
def activeReport (pub : Fin 11 → Word w) (i : Word w) (m : Memory w) : Report w :=
  let h := header pub
  let width := m (h + 9).val + i
  let dst := m (h + 11).val + i
  let total := m (h + 12).val
  ⟨pre pub m ++ [.tick, .tick, read m (h + 9), .tick, read m width, .tick, .tick,
    read m (h + 11), .tick, .tick, .tick, read m (h + 12), .write dst total, .tick,
    .write (h + 12) (total + m width.val), .tick], some (i + 1)⟩

/-- Final prefix report that adds the accumulated terminal width to the DFS row count, stores
the role-table displacement, and accepts. -/
def closeReport (pub : Fin 11 → Word w) (_i : Word w) (m : Memory w) : Report w :=
  let h := header pub
  ⟨pre pub m ++ [.tick, .tick, read m (h + 5), .tick, .tick, read m (h + 12),
    .tick, .tick, .tick, .write (h + 14) (m (h + 5).val + m (h + 12).val)], none⟩

@[simp] theorem active_result (pub : Fin 11 → Word w) (i : Word w) (m : Memory w) :
    (activeReport pub i m).result = some (i + 1) := rfl

@[simp] theorem close_result (pub : Fin 11 → Word w) (i : Word w) (m : Memory w) :
    (closeReport pub i m).result = none := rfl

theorem active_cost (pub : Fin 11 → Word w) (i : Word w) (m : Memory w) :
    (activeReport pub i m).probes = 7 ∧ (activeReport pub i m).events.length = 29 := ⟨rfl, rfl⟩

theorem close_cost (pub : Fin 11 → Word w) (i : Word w) (m : Memory w) :
    (closeReport pub i m).probes = 4 ∧ (closeReport pub i m).events.length = 23 := ⟨rfl, rfl⟩

theorem active_image (pub : Fin 11 → Word w) (i : Word w) (m : Memory w) :
    after m (activeReport pub i m).events = after m (SliceRAM.prefixEvents (data pub m) i m) :=
  rfl

theorem close_image (pub : Fin 11 → Word w) (i : Word w) (m : Memory w) :
    let h := header pub
    after m (closeReport pub i m).events =
      writeMemory m (h + 14) (m (h + 5).val + m (h + 12).val) := rfl

private theorem step (pub : Fin 11 → Word w) (c : Config w 41 7) :
    (table.instantiate w pub).program.step c = (instruction w c.pc).run pub c := by
  change ((instruction 6 c.pc).resize w).run pub c = _
  rw [resize_instruction]


private theorem step_at (pub : Fin 11 → Word w) (j : Fin 41) {c : Config w 41 7} (pc : c.pc = j) :
    (table.instantiate w pub).program.step c = (instruction w j).run pub c :=
  (step pub c).trans (by rw [pc])

private theorem jump_no (pub : Fin 11 → Word w) {c : Config w 41 7} (pc : c.pc = 12)
    (ne : c.reg 0 ≠ c.reg 3) :
    (table.instantiate w pub).program.step c = .localStep {c with pc := 13} := by
  rw [step_at pub 12 pc]
  change CallAction.localStep {c with pc := if c.reg 0 = c.reg 3 then 30 else 13} = _
  rw [ite_eq_right ne]

private theorem jump_yes (pub : Fin 11 → Word w) {c : Config w 41 7} (pc : c.pc = 12)
    (eq : c.reg 0 = c.reg 3) :
    (table.instantiate w pub).program.step c = .localStep {c with pc := 30} := by
  rw [step_at pub 12 pc]
  change CallAction.localStep {c with pc := if c.reg 0 = c.reg 3 then 30 else 13} = _
  rw [ite_eq_left eq]

set_option maxRecDepth 4096 in
/-- Exact native execution of the one-arc visit. -/
theorem active (pub : Fin 11 → Word w) (i : Word w) (m : Memory w)
    (hi : i ≠ m (header pub + 8).val) :
    let M := table.instantiate w pub
    execute M.program 30 (M.program.start i) m [] = some (activeReport pub i m) := by
  apply execute_iff.mpr
  refine ⟨?_, ?_, rfl⟩
  · apply Guessed.step (step_at pub 0 rfl)
    apply Guessed.step (step_at pub 1 rfl)
    apply Guessed.step (step_at pub 2 rfl)
    apply Guessed.step (step_at pub 3 rfl)
    apply Guessed.step (step_at pub 4 rfl)
    apply Guessed.step (step_at pub 5 rfl)
    apply Guessed.step (step_at pub 6 rfl)
    apply Guessed.step (step_at pub 7 rfl)
    apply Guessed.step (step_at pub 8 rfl)
    apply Guessed.step (step_at pub 9 rfl)
    apply Guessed.step (step_at pub 10 rfl)
    apply Guessed.read (step_at pub 11 rfl)
    apply Guessed.step (jump_no pub rfl hi)
    apply Guessed.step (step_at pub 13 rfl)
    apply Guessed.step (step_at pub 14 rfl)
    apply Guessed.read (step_at pub 15 rfl)
    apply Guessed.step (step_at pub 16 rfl)
    apply Guessed.read (step_at pub 17 rfl)
    apply Guessed.step (step_at pub 18 rfl)
    apply Guessed.step (step_at pub 19 rfl)
    apply Guessed.read (step_at pub 20 rfl)
    apply Guessed.step (step_at pub 21 rfl)
    apply Guessed.step (step_at pub 22 rfl)
    apply Guessed.step (step_at pub 23 rfl)
    apply Guessed.read (step_at pub 24 rfl)
    apply Guessed.write (step_at pub 25 rfl)
    apply Guessed.step (step_at pub 26 rfl)
    apply Guessed.write (step_at pub 27 rfl)
    apply Guessed.step (step_at pub 28 rfl)
    exact Guessed.done (step_at pub 29 rfl)
  · simp [activeReport, pre, read, Correct, update]

set_option maxRecDepth 4096 in
/-- Exact native execution of the terminal role-offset publication. -/
theorem close (pub : Fin 11 → Word w) (i : Word w) (m : Memory w)
    (hi : i = m (header pub + 8).val) :
    let M := table.instantiate w pub
    execute M.program 30 (M.program.start i) m [] = some (closeReport pub i m) := by
  apply execute_iff.mpr
  refine ⟨?_, ?_, rfl⟩
  · apply Guessed.step (step_at pub 0 rfl)
    apply Guessed.step (step_at pub 1 rfl)
    apply Guessed.step (step_at pub 2 rfl)
    apply Guessed.step (step_at pub 3 rfl)
    apply Guessed.step (step_at pub 4 rfl)
    apply Guessed.step (step_at pub 5 rfl)
    apply Guessed.step (step_at pub 6 rfl)
    apply Guessed.step (step_at pub 7 rfl)
    apply Guessed.step (step_at pub 8 rfl)
    apply Guessed.step (step_at pub 9 rfl)
    apply Guessed.step (step_at pub 10 rfl)
    apply Guessed.read (step_at pub 11 rfl)
    apply Guessed.step (jump_yes pub rfl hi)
    apply Guessed.step (step_at pub 30 rfl)
    apply Guessed.step (step_at pub 31 rfl)
    apply Guessed.read (step_at pub 32 rfl)
    apply Guessed.step (step_at pub 33 rfl)
    apply Guessed.step (step_at pub 34 rfl)
    apply Guessed.read (step_at pub 35 rfl)
    apply Guessed.step (step_at pub 36 rfl)
    apply Guessed.step (step_at pub 37 rfl)
    apply Guessed.step (step_at pub 38 rfl)
    apply Guessed.write (step_at pub 39 rfl)
    exact Guessed.done (step_at pub 40 rfl)
  · simp [closeReport, pre, read, Correct, update]

end PairSimulation.TerminalPrefix.Worker

end VPVNP
end Computability
end OAI

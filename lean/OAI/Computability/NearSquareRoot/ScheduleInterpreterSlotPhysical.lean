import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotInstallDriver
import OAI.Computability.IntegerMultiplication.SM.Output

/-! # The fixed physical scheduler, including its one-time initialization

The remaining input to the scheduler theorem consists of executions of one
raw Turing table reading a unary index. Every other component of the machine
is constructed: literal input setup, common blank cells, guard, indexed
clock, rollback, literal publication, and the unbounded outer search.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.IndexedSlot.Source
open IntegerMultiplication
variable {A Q I : Type} [Finite A] [DecidableEq A] [Fintype I] [DecidableEq I]
variable (s : Source A Q I)

/-- The geometric search and its setup have absolute numerical charges for
all slot indices and all bit lengths. -/
theorem physical_implementation {K p : ℕ} (runs : s.Runs lower upper K p) :
    s.physicalDriver.Implements 16 (SlotCost.coefficient I (4*Fintype.card I) 2) 120 K p := by
  have c : s.Comparison lower upper (4*Fintype.card I) K p :=
    { runs with
      origin := by intro n j; simp [lower,upper]; omega
      widths := widths I }
  exact s.implementation lower upper c _ _
    (fun n x => s.prepare n x ⟨fun b => (runs.letters.2.1 b).2,runs.letters.2.2⟩ runs.separate.2.2)

/-- A single finite raw interpreter with a polynomial fallback and fixed-index
near-square-root comparison runs gives the independently specified uniform
machine, with exact binary output and one absolute linear-space constant. -/
theorem uniformMultiplicationSpec [Finite Q] {K p : ℕ} (runs : s.Runs lower upper K p) :
    UniformMultiplicationSpec :=
  s.physicalDriver.uniformMultiplicationSpec (s.physical_implementation runs)

end Uniform.IndexedSlot.Source

end NearSquareRoot
end Computability
end OAI

import OAI.Hierarchy.DescentGLPhysicalHardware
import OAI.Hierarchy.DescentGlobalControlBill

namespace OAI
/-! # Uniform hardware and execution price of the central binary layout search -/

namespace Hierarchy.DescentCompiler
open DescentGL.PhysicalTrajectory ProtocolRAM

/-- Counts the emitted labels, registers and public slots of the same physical
program whose chronological score computation chooses the measured layout. -/
theorem global_solver_hardware (w m base : ℕ) (bank : ℕ→ℕ) :
    let p:=DescentGL.PhysicalTrajectory.program w m base bank
    CheapCode p ∧ p.labels+p.registers+p.slots ≤ 8000*2^(5*m) ∧
      time m base bank m+DescentGLPermutationRAM.clock m ≤ 4000*2^(5*m) := by
  have cpu:=global_solver_clock m base bank
  refine ⟨DescentGL.PhysicalTrajectory.program_cheap w m base bank,?_,cpu⟩
  exact (DescentGL.PhysicalTrajectory.program_size w m base bank).trans
    ((Nat.mul_le_mul_left 2 cpu).trans_eq (by rw [←Nat.mul_assoc]))

end Hierarchy.DescentCompiler

end OAI

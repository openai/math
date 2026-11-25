import OAI.Hierarchy.DescentColonyWinningSlabRead
import OAI.Hierarchy.DescentColonyCandidateHardware

namespace OAI
/-! # Instruction and ROM costs for the full selected outgoing slab tape -/

noncomputable section
namespace Hierarchy.DescentColonies
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open DescentGL (Bits)
variable {G H k : ℕ}

theorem Materialized.program_bounded (w base : ℕ) (raw : Fin G→Fin H→ℕ) (a : Bits k) :
    let P := Materialized.program w base raw a
    CandidateRAM.Bounded P.text P.ticks := by
  apply CandidateRAM.batch_bound (Materialized.step w base raw a)
  intro i
  exact CandidateRAM.scan_bound _ _ _ _ (Nat.two_pow_pos _)

namespace WinningSlabs.Selected

theorem program_bounded (w base : ℕ) (raw : Fin G→Fin H→ℕ) (a : Bits k) :
    let P := program w base raw a
    CandidateRAM.Bounded P.text P.ticks := by
  apply CandidateRAM.seq_bound (Materialized.program_bounded w base raw a)
  apply CandidateRAM.passes_bound
  intro p hp
  rw [(world_pass k (slabBase G H k base) (flags (G:=G) (H:=H) base) (amounts k base) hp).1]
  exact Nat.two_pow_pos _

theorem program_size (w base : ℕ) (raw : Fin G→Fin H→ℕ) (a : Bits k) :
    let P := program w base raw a
    P.text.labels+P.text.registers+P.text.slots≤4*P.ticks := (program_bounded w base raw a).size

theorem program_cheap (w base : ℕ) (raw : Fin G→Fin H→ℕ) (a : Bits k) :
    CheapCode (program w base raw a).text := (program_bounded w base raw a).cheap

end WinningSlabs.Selected
end Hierarchy.DescentColonies

end
end OAI

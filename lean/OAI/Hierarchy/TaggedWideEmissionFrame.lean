import OAI.Hierarchy.ProtocolRAMEmit

namespace OAI
/-! # Transport of the nine emitted words over a RAM write frame -/

namespace Hierarchy.TaggedShorterControlHistory
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAMEmit
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Classical Fin.CommRing

/-- After the static mask/ID/width publisher updates its own banks, the
retained nine-column row table still constitutes the original emission.
The memory below and above this table may contain all scratch and metadata
of the intervening native procedures. -/
theorem emitted_of_frame {W n : ℕ} (dst : ℕ) (rows : Fin n → ProtocolRAMEmit.Row)
    (initial after : Memory W)
    (frame : ∀ j,dst≤j → j<dst+9*n → after j=emitted dst rows initial j) :
    emitted dst rows after=after := by
  funext j
  by_cases inside : dst≤j ∧ j<dst+9*n
  · rw [frame j inside.1 inside.2]
    simp only [emitted,fillSegment]
    split_ifs <;> first | rfl | omega
  · have low : ¬ (dst≤j ∧ j<dst+3*n) := by omega
    have mid : ¬ (dst+3*n≤j ∧ j<dst+3*n+3*n) := by omega
    have high : ¬ (dst+6*n≤j ∧ j<dst+6*n+3*n) := by omega
    simp [emitted,fillSegment,low,mid,high]

end Hierarchy.TaggedShorterControlHistory

end OAI

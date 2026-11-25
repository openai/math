import OAI.Hierarchy.DescentInitialDatePorts
import OAI.Hierarchy.DescentRegisterTimelineCore

namespace OAI
/-! # Public register addresses and memory along a sequence of native dates -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
open scoped Classical

variable {w : ℕ} {Cut : ℕ→Type*} (issue : ∀i,Cut i→Position→Move w→Prop) (initial : Position)

theorem held_after {F P : Type} [Field F] {D age grain deg wire hist k : ℕ}
    {bits : P→ℕ} {W : MarkedWorld F D P bits} {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule}
    (r : Reached W G q ε S k (age+1) grain deg wire hist) (m : Memory w) (c : Cut age) (move : Move w)
    (hit : issue age c (position issue initial age) move) (later : (position issue initial age).floor ≤ move.next.floor)
    (unique : ∀d t,issue age d (position issue initial age) t→t=move)
    (observed : ∃out,move.code.Runs (DateCode.history (date issue initial) m age) out ∧ move.next.ports.held r move.next.floor out) :
    (position issue initial (age+1)).ports.held r
      (DescentDatedAddressBook.floor initial.floor (span issue initial) (age+1))
      (DateCode.history (date issue initial) m (age+1)) :=by
  obtain ⟨code,next⟩:=date_at issue initial age c move hit later unique
  rw [←position_floor issue initial,next]
  apply DateCode.history_event
  rwa [code]

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI

import OAI.Computability.VPVNP.CompressorShrinkSlotFixedOperands
import OAI.Computability.VPVNP.CompressorWindowPrepared

/-! # Control and header addresses protected during a shrinking slot window -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlotCalendar

open BurstRAM BlockPlanner DescriptorSpace Schedule
open scoped Fin.CommRing

variable {w : ℕ} (A : Script) (L : DescriptorSpace.Layout) (base : Word w)
local notation "pt" => Workspace.ports (Schedule.arity A.catalog) base
local notation "H" => levelStart L 0
local notation "pitchCell" => Fin.val (Schedule.Ports.directory pt-1)

/-- Numeric layout evidence for a single repeated shrinking block. The
two headers and the selected score cell are read by the actual planners. -/
structure Boundary (t step role slotStart slotEnd copyStart score : ℕ) : Prop where
  arity : Schedule.arity A.catalog = L.shape.arity
  baseValue : base.val = L.base
  fits : H < 2^w
  blockRoom : A.initial.length+(t+1)*A.block.length ≤ directoryRows L
  rowsBefore : (pt).rows.val < H
  pitchBefore : pitchCell < H
  roleHigh : H ≤ role
  roleBefore : role ≤ slotStart
  oldBefore : levelStart L (A.levelsPerBlock*t+step)+66 ≤ slotStart
  slotBefore : slotEnd ≤ levelStart L (A.levelsPerBlock*t+(step+1))
  headerBefore : levelStart L (A.levelsPerBlock*t+(step+1))+66 ≤ copyStart
  scoreHigh : H ≤ score
  scoreBefore : score < slotStart
  oldFits : levelStart L (A.levelsPerBlock*t+step)+66 ≤ 2^w
  nextFits : levelStart L (A.levelsPerBlock*t+(step+1))+66 ≤ 2^w

variable {A L base} {t step role slotStart slotEnd copyStart score : ℕ}
variable (bound : Boundary A L base t step role slotStart slotEnd copyStart score)
local notation "old" => levelStart L (A.levelsPerBlock*t+step)
local notation "new" => levelStart L (A.levelsPerBlock*t+(step+1))
local notation "roots" => RootCell pitchCell old new score

include bound in
/-- Actual slot writes and canonical copies preserve every planner root
and the row-total cell. -/
theorem Boundary.untouched {x count : ℕ} (live : slotStart ≤ slotEnd)
    (written : (slotStart ≤ x ∧ x < slotEnd) ∨ (copyStart ≤ x ∧ x < copyStart+count)) :
    ¬ (roots x ∨ x=(pt).rows.val) := by
  have h₀ := bound.roleHigh
  have h₁ := bound.roleBefore
  have h₂ := bound.oldBefore
  have h₃ := bound.slotBefore
  have h₄ := bound.headerBefore
  have h₅ := bound.scoreBefore
  have hp := bound.pitchBefore
  have hr := bound.rowsBefore
  rintro ((p|o|n|s)|r) <;> omega

end CompressorRecords.ShrinkSlotCalendar

end VPVNP
end Computability
end OAI

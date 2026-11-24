import OAI.Computability.VPVNP.CompressorInitialScheduled
import OAI.Computability.VPVNP.CompressorInitialProbeRate
import OAI.Computability.VPVNP.CompressorCurrentResident

/-! # The stored cursor state at the first selected compression pass

The four physical cursor workers publish the degree, site and lane counts,
the six incidence columns, the table heads and the initial DFS base. These
words and the zero cursor role initialize the selected directory history.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.ScheduledTrace

open BurstRAM Compression DescriptorSpace Schedule BlockPlanner BlockHeaderRun
open PairSimulation.LocalHistory PairSimulation.TraversalRows PairSimulation.TraversalRoles
open scoped Fin.CommRing

variable {w : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
  {base positions blocks cap small b l width n : ℕ} {pub : Fin 11 → Word w} {m : Memory w}
  {X : State (S.degreeExponent 0) l}

local notation "L" => BlockProgram.layout B base positions blocks
local notation "a₀" => S.degreeExponent 0
local notation "A" => BlockProgram.script B

/-- The persistent cursor frame read by later passes from the first level. -/
def cursorFrame (alloc : Layout) (a b l width : ℕ) : Fin 8 → Word w :=
  CursorRAM.ScheduleInit.inputs (CursorRAM.encode w (directoryBase alloc)) (CursorRAM.encode w 1) b l a width (incidenceStart alloc 0)

variable (init : InitialInterval B base positions blocks cap small b l width pub m)

theorem InitialInterval.boundary {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
    (cursor : BlockStartupPrefix.Resident L a₀ b l width n (pub 2) m X)
    (fit : endAddress L < 2^w) :
    Boundary (CurrentResident.resident B f hf ⟨leafLayer (siteOrder X),.cursor⟩ L (endAddress L) n (cursorFrame L a₀ b l width))
      pub (levelWords L : Word w) (directoryRows L) 4 [] X init.interval.segment.memory := by
  exact ⟨init.bank,init.tag,init.ordinal,init.total,init.stride,
    CurrentResident.initial_live cursor init.agrees (by change 0 < 1+(S.steps+1)*blocks; omega) (by change 14 ≤ 54; decide) fit⟩

/-- Coefficient depending only on the fixed script, independent of the
length, memory, row count and group-specific histogram. -/
def initialRate (B : S.Templates) :=
  let script := BlockProgram.script B
  let a := S.degreeExponent 0
  (7*2^a + InitialProbeRate.fixed (BlockProgram.layout B 0 0 0) a)*(arity script.catalog+3) +
    4*(Online.Run.maxReads script.plan+4*arity script.catalog+26)

theorem InitialInterval.rate (cursor : BlockStartupPrefix.Resident L a₀ b l width n (pub 2) m X)
    : RAMBuckets.cost Report.probes init.interval.source.logs ≤ initialRate B*(positions+1) := by
  apply init.cost.trans
  have rows : CursorRAM.rowCount b l a₀ = positions*2^a₀ := by
    change ((b+l)*2^b*2^l)*2^a₀ = _
    exact congrArg (· * 2^a₀) cursor.positions
  unfold initialCost initialRate
  rw [(InitialProbeRate.raw L a₀ b l width m).2,rows,InitialProbeRate.fixed_layout]
  let g := arity (Script.catalog (BlockProgram.script B))+3
  let h := InitialProbeRate.fixed (BlockProgram.layout B 0 0 0) a₀
  let ov := 4*(Online.Run.maxReads (Script.plan (BlockProgram.script B))+4*arity (Script.catalog (BlockProgram.script B))+26)
  change (7*(positions*2^a₀)+h)*g+ov ≤ ((7*2^a₀+h)*g+ov)*(positions+1)
  nlinarith only [Nat.zero_le (h*g*positions), Nat.zero_le (ov*positions), Nat.zero_le (7*2^a₀*g)]

end CompressorRecords.ScheduledTrace

end

end VPVNP
end Computability
end OAI

import OAI.Hierarchy.DescentArchiveCellRead
import OAI.Hierarchy.DescentPackedHistoryMass

namespace OAI
/-! # Initial occupancy and the original paid count on each later register -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentKernelHistory DescentLocalArchiveOrder DescentCompiler
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d k wire hist : ℕ} {bits : P→ℕ}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule}
/-- Measured metadata field zero is an occupancy bit at startup and a paid-row
mask at every ordinary or reset output. The original venue stores the number of
funded records in each group and block of the genuine reached actor. -/
def archiveFlag {W : MarkedWorld F d P bits} {i z D : ℕ} (r : Reached W G q ε S k i z D wire hist)
    (B : BitDescription W) (rank : Local B) (ports : DatePorts) (room : DatePorts.RangeRoom ports r B)
    (x : Fin (2^ports.venue.k)) (n : Fin ports.nodes) (h : Fin ports.operandHosts) (g : Fin ports.venue.groups) : ℕ :=
  if i=0 then if (DatePorts.slotAt ports r B rank room x n h g).isSome then 1 else 0
  else if actor : ∃v : r.V,(r.vertex v).val=h.val then
    let total:=PackedCensus.histories W r.placement.pos r.placement.block r.placement.records
      (g.cast room.groups.symm,actor.choose) (x.cast (congrArg (2^·) room.radix.symm))
    if n.val<total then 1 else 0
  else 0

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI

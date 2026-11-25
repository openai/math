import OAI.Computability.BorderVNP.DiagonalScheduledGuardedReports
import OAI.Computability.BorderVNP.DiagonalReceivedCoreSound

/-! # Passing of the actual received cells on an original guarded source -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing CellSparse Packing.BottomReports DiagonalTallyCellReports
open RoutingISA RoutingISA.Evaluator CompactMachine CellMacro.Generator
open scoped Classical

variable {D n d blocks b h K s R dim width word order batch M E Z high table rows coeff k B j : ℕ}
    {P J : Type} [Fintype P] [Fintype J] {bits : P → ℕ} {N : Network D P bits}
    (dir : CoreDirectory N n d blocks b h K R) (pin : Ports bits) (owner : Fin dir.siteRows → ℕ)
    (host : J ↪ N.Site) (bundle : J → Bundle) (origins : Fin dir.cells → List J)
    (v : dir.Route s × dir.Bank) {id : TableEntry n b h K s → ℕ} {gen : Fragment IO}
    (X : UncheckedCandidate id gen order word (R+1) dim width) (received : ReceivedRows X.layout dir.cells)
    (assigned : X.assigned=received.assigned N dir.cell dir.siteID dir.edgeID dir.portID dir.programs dir.owners
      dir.slot pin owner (fun c => (origins c).map bundle) v.1.val v.2)
    (source : ReceivedBounds received N dir.cell dir.siteID owner dir.programs host bundle origins M E Z high table rows
      (coeff*(TeamScales.logWidth batch order+1)^k))
    (scheduled : Diagonal.PrivateCellBudgetAt 3076 table (B+10) (j+1) rows coeff k order batch)

include assigned source scheduled in
/-- This provides the original-input passing proof required by the native
report completion, on the scheduled processor and its actual compact rows. -/
theorem CoreDirectory.receivedPassing (hn : 1≤order) (hr : 1≤batch) (format : 9≤rows)
    (localCap : M≤TeamScales.width order (1/5)) (privateCap : E≤TeamScales.width order (1/4))
    (positive : 0<word) (small : word≤order) (idBits : high.size+1≤B*(TeamScales.logWidth batch order+1)^j)
    (marked : 3*M+Z≤4*(M+E+1)^3) (guard : dir.Guard pin v) :
    ∀ t c, c ∈ X.assigned t → c.Passing word order := by
  have live := (dir.guard_iff_received pin owner source.ownerID v (received.countReports N dir.cell dir.programs)).mp guard
  have pass := scheduled_guarded_reports scheduled hn hr format localCap privateCap positive small idBits marked received
    N dir.cell dir.siteID dir.edgeID dir.portID dir.programs dir.owners dir.slot pin owner host bundle origins source v.1.val v.2 live
  rw [assigned]
  exact pass

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI

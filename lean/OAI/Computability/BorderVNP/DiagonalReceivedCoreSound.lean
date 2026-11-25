import OAI.Computability.BorderVNP.DiagonalPositiveCoreReceived
import OAI.Computability.BorderVNP.DiagonalPositiveCoreReports
import OAI.Computability.BorderVNP.DiagonalNativeCoreDirectory
import OAI.Computability.BorderVNP.DiagonalGuardedOwnerCongr

/-! # Soundness on every physically assigned row before the private call -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited CellMacro.Generator
open RoutingISA.Evaluator DiagonalTallyCellReports
open scoped Classical

variable {D C ns ne np n d blocks b h K s T dim digits word input : ℕ} {P Team : Type} [Fintype P]
    {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (state : Site.Programs N) (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (ports : Ports bits)
    (owner : Fin ns → ℕ) (bottom : Fin C → List Bundle)
    (v : PinnedRaw (s:=s) N cell state owners slot)
    {id : TableEntry n b h K s → ℕ} {gen : Fragment IO} (A : UncheckedCandidate id gen input word T dim digits)
    (R : ReceivedRows A.layout C)
    (same : A.assigned = R.assigned N cell siteID edgeID portID state owners slot ports owner bottom v.1.val v.2)
    (stored : ∀ x, owner (siteID x)=(cell x).val)
    (schema : ∀ x, (state x).program.Schema) (locality : ∀ x, (state x).birth.Local)
    (relative : ∀ x, (state x).program.RelativeBoxes) (sign : ∀ x, (state x).program.SignFree)

include same stored schema locality relative sign in
/-- A nonzero product on arbitrary proposed report/tally fields forces every
original signed directory to have passed. Only the actual received-cell order
is required, and the hypothesis holds before the local reports have been
screened. Both endpoint padding tests come from the stored routed assignment. -/
theorem ReceivedRows.guarded_of_privateWeight (r : NativeReports A.assigned) (claim : Fin (T*dim*digits) → Bool)
    (weight : (A.joined r claim (A.candidate r claim).1).privateWeight (A.candidate r claim).2 ≠ 0) :
    GuardedCores N cell siteID edgeID portID state owners slot ports owner (R.countReports N cell state) v.1.val v.2 := by
  have rows : OriginalRows N cell siteID edgeID portID state owners slot ports owner (R.countReports N cell state)
      v.1.val v.2 A.assigned := by
    rw [same]
    exact OriginalRows.ofReceived R N cell siteID edgeID portID state owners slot ports owner bottom v.1.val v.2 sign
  exact OriginalRows.guarded_of_nonzero N cell siteID edgeID portID state owners slot ports owner
    (R.countReports N cell state) v.1.val v.2 A.assigned rows stored (fun x => (state x).size) schema
    (fun x => (state x).retention.locality (locality x)) relative
    (A.joined r claim (A.candidate r claim).1) (A.candidate r claim).2 r (A.image r claim)
    ((routedPins_iff N cell edgeID state owners slot v.1.val v.2).mp v.1.property) weight

section

variable {N} {teamsPred : ℕ} (B : CoreDirectory N n d blocks b h K teamsPred)
    (pin : Ports bits) (reportedOwner : Fin B.siteRows → ℕ) (originalBundles : Fin B.cells → List Bundle)
    (physical : ∀ x, reportedOwner (B.siteID x) = (B.cell x).val)
    (legal : ∀ x, (B.programs x).birth.Local ∧ (B.programs x).program.Schema ∧
      (B.programs x).program.RelativeBoxes ∧ (B.programs x).program.SignFree)

include physical in
/-- The normalized source guard and the received guard have identical
acceptance on every proposed private bank, before checking its report. -/
theorem CoreDirectory.guard_iff_received (v : B.Route s × B.Bank) (reports : Fin B.cells → List (List ℕ)) :
    B.Guard pin v ↔ GuardedCores N B.cell B.siteID B.edgeID B.portID B.programs B.owners B.slot
      pin reportedOwner reports v.1.val v.2 :=
  guardedCores_congr_occupied N B.cell B.siteID B.edgeID B.portID B.programs B.owners B.slot pin
    B.owner reportedOwner (fun x => (B.owner_site x).trans (physical x).symm)
    (fun _ => []) reports v.1.val v.2

include physical legal in
/-- A native nonzero product on the physically received rows forces the
fixed source guard, even if an empty published owner row was malformed or
the visiting team's count-field addresses depended on its chosen schedule. -/
theorem CoreDirectory.receivedSound (v : B.Route s × B.Bank)
    (A : UncheckedCandidate id gen input word (teamsPred+1) dim digits)
    (R : ReceivedRows A.layout B.cells)
    (same : A.assigned = R.assigned N B.cell B.siteID B.edgeID B.portID B.programs B.owners B.slot
      pin reportedOwner originalBundles v.1.val v.2)
    (r : NativeReports A.assigned) (claim : Fin ((teamsPred+1)*dim*digits) → Bool)
    (weight : (A.joined r claim (A.candidate r claim).1).privateWeight (A.candidate r claim).2 ≠ 0) : B.Guard pin v := by
  have actual := R.guarded_of_privateWeight N B.cell B.siteID B.edgeID B.portID B.programs B.owners B.slot pin
    reportedOwner originalBundles v A same physical (fun x => (legal x).2.1) (fun x => (legal x).1)
    (fun x => (legal x).2.2.1) (fun x => (legal x).2.2.2) r claim weight
  exact (B.guard_iff_received pin reportedOwner physical v (R.countReports N B.cell B.programs)).mpr actual

end

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.DiagonalReceivedCoreSound
import OAI.Computability.BorderVNP.DiagonalReceivedReportUseReadback

/-! # The initial source guard and bit extent of an actual received cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited CellSparse DiagonalTallyCellReports
open scoped Classical

variable {D n d blocks b h K R symbols w order : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
  {N : Network D P bits} (B : CoreDirectory N n d blocks b h K R) {chart : Fin (R+1) → ReportLayout}
  (rc : ReceivedRows chart B.cells) {l : ReportLayout} (rows : ReceivedRows (fun _ : Fin (R+1) => l) B.cells)
  (pin : Ports bits) (bundles : Fin B.cells → List Bundle)
  (v : B.Route symbols × B.Bank)

local notation3 (prettyPrint := false) "assigned" => rc.assignedAt N B.cell B.siteID B.edgeID B.portID B.programs
  B.owners B.slot pin B.owner bundles v.1.val v.2

/-- Every passing received cell satisfies its original guard on the actual private
bank. Together with both routed endpoint checks this gives the source guard. -/
theorem CoreDirectory.guard_of_received_passing
    (pass : ∀ j : (t : Fin (R+1)) × Fin (rc.cells t).length, (assigned j.1 j.2).Passing w order) :
    B.Guard pin v := by
  apply (B.guard_iff_received pin B.owner B.owner_site v (rc.countReports N B.cell B.programs)).mpr
  refine ⟨(routedPins_iff N B.cell B.edgeID B.programs B.owners B.slot v.1.val v.2).mp v.1.property,?_⟩
  intro c
  obtain ⟨j,rfl⟩ := rc.order.surjective c
  obtain ⟨t,i⟩ := j
  refine ⟨(assigned t i).observations,?_⟩
  have observed := (pass ⟨t,i⟩).seen []
  simp only [List.append_nil] at observed
  rw [rc.assignedAt_directory,rc.assignedAt_pre] at observed
  exact observed

/-- The private and supplied widths stored in the published row account for the
entire pre-report bit vector, including the immutable staging words. -/
theorem CoreDirectory.received_extent (t : Fin (R+1)) (i : Fin (rc.cells t).length)
    (widths : let c := (rc.order ⟨t,i⟩).val
      let row := (rc.cells t).get i
      row.supplied = suppliedSize N (fun x => (B.cell x).val) c ∧
        row.privateWires = guessedSize N (fun x => (B.cell x).val) c +
          siteSize N (fun x => (B.cell x).val) c (placedSize N B.programs)) :
    ((rc.cells t).get i).privateWires+((rc.cells t).get i).supplied =
      (assigned t i).privateWires+(assigned t i).boundary.length := by
  rw [widths.1,widths.2]
  simp only [ReceivedRows.assignedAt, FinalCell.assignedReport, FinalCell.privateBits, List.length_ofFn]

open Site.Programs Diagonal.CellEntries

/-- On the passing received rows, the native staged bank itself supplies
the complete path guards for the given model of its site programs. -/
theorem CoreDirectory.corePassed_of_received {J Param Gadget : Type} (host : J ↪ N.Site) (slabs : J → Slab)
    (mult : J → ℕ) (widths : ∀ j, (B.programs (host j)).birth.work = mult j*(slabs j).stride)
    (number : Gadget ↪ ℕ) (tags : BottomChoices slabs mult → N.Tables (Entry Param Gadget))
    (model : ∀ z, TagModels N B.edgeID B.portID B.programs (tags z) number
      (carryPred host (birthPredicate slabs mult z)))
    (birthLocal : ∀ x, (B.programs x).birth.Local) (schema : ∀ x, (B.programs x).program.Schema)
    (relative : ∀ x, (B.programs x).program.RelativeBoxes)
    (pass : ∀ j : (t : Fin (R+1)) × Fin (rc.cells t).length, (assigned j.1 j.2).Passing w order) :
    CorePassed N B.cell B.siteID B.edgeID B.portID B.programs host slabs mult widths
      B.owners B.slot pin number tags model v.1.val v.2 := by
  exact (guardedCores_iff N B.cell B.siteID B.edgeID B.portID B.programs host slabs mult widths B.owners
    B.slot pin number tags model B.owner (fun _ => []) B.owner_site birthLocal schema relative v.1.val v.2).mp
    (B.guard_of_received_passing rc pin bundles v pass)

section CommonChart

local notation3 (prettyPrint := false) "sourceAt" => rows.assignedAt N B.cell B.siteID B.edgeID B.portID B.programs
  B.owners B.slot pin B.owner bundles v.1.val v.2
local notation3 (prettyPrint := false) "originalSize" => placedSize N B.programs
local notation3 (prettyPrint := false) "originalBank" c => bank N B.cell c originalSize
  (privateWires N B.cell originalSize c (v.2 c)) (privateStaging N B.cell originalSize c (v.2 c))
  (pathSupply N B.cell B.edgeID B.portID B.owners B.slot pin v.1.val c)

/-- Loading the report tape preserves every private and supplied bit extent
at the exact global numeral of its published team-local row. -/
theorem CoreDirectory.returnedBank_extent
    (tape : Fin (R+1) → ℕ → Bool) (start : Fin (R+1) → ℕ)
    (extent : ∀ j : (t : Fin (R+1)) × Fin (rows.cells t).length,
      ((rows.cells j.1).get j.2).privateWires+((rows.cells j.1).get j.2).supplied =
        (sourceAt j.1 j.2).privateWires+(sourceAt j.1 j.2).boundary.length) (c : Fin B.cells) :
    (originalBank c).length = (rows.reportedWithTape tape start c).privateWires +
      (rows.reportedWithTape tape start c).supplied := by
  obtain ⟨⟨t,i⟩,rfl⟩ := rows.order.surjective c
  have pre := rows.assignedAt_pre N B.cell B.siteID B.edgeID B.portID B.programs B.owners B.slot
    pin B.owner bundles v.1.val v.2 t i
  rw [←pre, rows.reportedWithTape_at]
  have len : (sourceAt t i).pre.length=(sourceAt t i).privateWires+(sourceAt t i).boundary.length := by
    simp only [AssignedCell.pre,List.length_append,List.length_ofFn]
  exact len.trans (extent ⟨t,i⟩).symm

end CommonChart

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.DiagonalReceivedReportExtent
import OAI.Computability.BorderVNP.DiagonalSignedReportEntry
import OAI.Computability.BorderVNP.DiagonalSameReportVisits

/-! # True source-supplied and report widths at every final physical cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing Packing.CellAddresses Packing.BottomReports Packing.Inherited Site.Programs CellSparse
open RoutingISA DiagonalTallyCellReports

variable {T C D ns : ℕ} {P J : Type} [Fintype P] [Fintype J] {bits : P → ℕ} {layout : Fin T → ReportLayout}
    (R : ReceivedRows layout C) (N : Network D P bits) (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (owner : Fin ns → ℕ) (state : Site.Programs N)
    (host : J ↪ N.Site) (bundle : J → Bundle) (origins : Fin C → List J)
    {M E Z high table rows digitBound : ℕ}
    (bound : ReceivedBounds R N cell siteID owner state host bundle origins M E Z high table rows digitBound)

include bound in
/-- The native call compiler's received bounds control the actual supplied wires and full
expanded report on every cell, including cells outside this team's output and empty cells.
The sparse input used to measure the two lengths may have arbitrary report bits. -/
theorem ReceivedBounds.report_supply_room {j : ℕ} (homes : Fin j → Fin C) (source : Fin j → ReportBundle)
    (g w : ℕ) (parameters : ∀ t,(layout t).gadgets=g ∧ (layout t).countWidth=w)
    (grouped : ∀ u i,((R.cells u).get i).bundles=(BundleDirectory.sourceRows homes (R.order ⟨u,i⟩).val).map source)
    (c : Fin C) :
    suppliedSize N (fun v => (cell v).val) c.val+
      (g*w+weightedCopies ((BundleDirectory.sourceRows homes c.val).map source))≤E := by
  let z := R.order.symm c
  let v := R.order z
  have toCell : v=c := R.order.apply_symm_apply c
  let row := (R.cells z.1).get z.2
  let field : SparseExterior.Field := ⟨suppliedSize N (fun s => (cell s).val) v.val,[],List.replicate row.tailWidth false⟩
  have limit := (ReceivedBounds.fieldInputs R N cell siteID owner state host bundle origins bound (u:=z.1) (i:=z.2)
    field rfl List.length_replicate).2.1
  change suppliedSize N _ v.val+(List.replicate row.tailWidth false).length≤E at limit
  rw [List.length_replicate] at limit
  have b : row.bundles=(BundleDirectory.sourceRows homes v.val).map source := grouped z.1 z.2
  change suppliedSize N _ v.val+((layout z.1).gadgets*(layout z.1).countWidth+(row.bundles.map ReportBundle.useCount).sum)≤E at limit
  simpa only [b,toCell,(parameters z.1).1,(parameters z.1).2,weightedCopies] using limit

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI

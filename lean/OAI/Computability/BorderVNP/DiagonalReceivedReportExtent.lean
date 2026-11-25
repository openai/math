import OAI.Computability.BorderVNP.DiagonalPositiveGuardedReports
import OAI.Computability.BorderVNP.PackedScheduledSparseCell

/-! # The true sparse-call size on an arbitrary report spelling -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing Packing.CellAddresses Packing.BottomReports Packing.Inherited
open Site.Programs CellSparse DiagonalTallyCellReports RoutingISA

variable {T C D ns : ℕ} {P J : Type} [Fintype P] [Fintype J] {bits : P → ℕ} {layout : Fin T → ReportLayout}
    (R : ReceivedRows layout C) (N : Network D P bits) (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (owner : Fin ns → ℕ) (state : Site.Programs N)
    (host : J ↪ N.Site) (bundle : J → Bundle) (origins : Fin C → List J)
    {M E Z high table rows digitBound : ℕ}
    (bound : ReceivedBounds R N cell siteID owner state host bundle origins M E Z high table rows digitBound)
    (u : Fin T) (i : Fin (R.cells u).length)

include bound in
/-- Counts and expanded uses in the tail are allocated on the received cell before
their bits are guessed. Replacing the whole report tape, even by values which
subsequently fail the validator, preserves the full sparse call's resource bounds. -/
theorem ReceivedBounds.fieldInputs (field : SparseExterior.Field)
    (width : field.width=suppliedSize N (fun v => (cell v).val) (R.order ⟨u,i⟩).val)
    (len : field.tail.length=((R.cells u).get i).tailWidth) :
    let bs := (origins (R.order ⟨u,i⟩)).map bundle
    (bs.map (fun x => count x.factors)).sum+bs.length ≤ 2*(M+1) ∧
      field.width+field.tail.length ≤ E ∧
      field.tail.length=(layout u).gadgets*(layout u).countWidth+(bs.map Bundle.useBits).sum ∧
      ∀ x ∈ bs, count x.factors ≤ x.header.cap ∧ x.header.copies ≤ 4*(M+E+1)^3 ∧
        x.header.boxBase+x.header.orig+x.header.cap ≤ 4*(M+E+1)^3 := by
  intro bs
  let c := R.order ⟨u,i⟩
  have resource := retained_call_bounds N (fun v => (cell v).val) (fun v => (state v).program) siteID host bundle
    bound.retained c.val M E (layout u).gadgets (layout u).countWidth (origins c) (bound.unique c)
    (bound.belongs c) (bound.copies c) bound.incoming (bound.publicLoad c) (bound.expandedLoad c) (bound.space u)
  have size : field.tail.length=(layout u).gadgets*(layout u).countWidth+(bs.map Bundle.useBits).sum := by
    rw [len,ReportCell.tailWidth,bound.uses u i]
  refine ⟨resource.1,?_,size,resource.2.2⟩
  simpa only [width,size,←Nat.add_assoc] using resource.2.1

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI

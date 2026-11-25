import OAI.Computability.BorderVNP.DiagonalPinnedGuards
import OAI.Computability.BorderVNP.DiagonalCanonicalReportDirectory
import OAI.Computability.BorderVNP.RoutingISASignedPrepSourceRows

/-! # The pinned source report rows of each routed cube assignment -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing CellMacro.Generator BorderVNP.Cube Physical Physical.NativeAssignments
open DiagonalTallyCellReports ReportDirectory

variable {D R bundles : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (ar : CubeArena.Layout) (N : Network D P bits) (cell : N.Site → Fin ar.cells)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (slot : LiveBit N cell ↪ Slot ar.n ar.header.d ar.header.blocks (ar.h*ar.b))
    (label : Fin ar.cells → Label (ar.n+1) ar.header.d)
    (charts : Fin (R+1) → ReportLayout) (home : Fin bundles → Fin ar.cells) (bodies : Fin bundles → ReportBundle)
    (supplied wires : ℕ → ℕ)

/-- Numeric owner of an original cell in the selected coordinate. The
report directory scans only its finite real cell range. -/
def routedOwnerWord (q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners) (c : ℕ) : ℕ :=
  if hc : c < ar.cells then (owners q.1 (label ⟨c,hc⟩ (chosen ar.b ar.s q.1))).val else 0

/-- The actual two-ended zero padding and the mathematical ordered cells
received by each team; all sampled report positions start at zero before
the native report choices are made. -/
noncomputable def routedSourceReports : SourceReports ar owners where
  pins := RoutedPins N cell owners slot
  layout _ := charts
  cells q u := sourceCells (charts u) home bodies u.val (routedOwnerWord ar owners label q)
    (fun c => ar.cellBank+c*ar.cellStride) supplied wires (fun _ _ _ => false)

/-- At every genuine cell the selection uses the declared coordinate of its
own labels and the owner of that coordinate on the actual routed selector. -/
theorem routedOwnerWord_at (q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners) (c : Fin ar.cells) :
    routedOwnerWord ar owners label q c.val=(owners q.1 (label c (chosen ar.b ar.s q.1))).val :=
  dite_eq_left c.isLt

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI

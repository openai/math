import OAI.Computability.BorderVNP.DiagonalSourceReceivedRows

/-! # The report proposal on a routed selection and all its receiving teams -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing CellMacro.Generator BorderVNP.Cube Physical Physical.NativeAssignments
open DiagonalTallyCellReports ReportDirectory

/-- A routed source selection satisfying the endpoint tests, together with its
original report assignment on every team. -/
abbrev SourceReports.Proposals {R : ℕ} {ar : CubeArena.Layout}
    {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
    (source : SourceReports ar owners) :=
  (q : Subtype source.pins) × source.actual q.val

variable {D R bundles : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (ar : CubeArena.Layout) (N : Network D P bits) (cell : N.Site → Fin ar.cells)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (slot : LiveBit N cell ↪ Slot ar.n ar.header.d ar.header.blocks (ar.h*ar.b))
    (label : Fin ar.cells → Label (ar.n+1) ar.header.d)
    (charts : Fin (R+1) → ReportLayout) (home : Fin bundles → Fin ar.cells) (bodies : Fin bundles → ReportBundle)
    (supplied wires : ℕ → ℕ)

local notation3 (prettyPrint := false) "dataRows" =>
  routedSourceReports ar N cell owners slot label charts home bodies supplied wires
local notation3 (prettyPrint := false) "received(" z ")" =>
  routedReceivedRows ar owners label charts home bodies supplied wires z
local notation3 (prettyPrint := false) "pinned" =>
  {v : Routed (b:=ar.b) (s:=ar.s) owners // RoutedPins N cell owners slot v}
local notation3 (prettyPrint := false) "ownerRows" =>
  (v : pinned) × ((u : Fin (R+1)) → ReportAssignments ((received(v.val)).cells u))

/-- The original pinned selection and its issued reports are exactly the same
selection with the received assignments on each team's own cell list. -/
def routedReportProposals : (dataRows).Proposals ≃ ownerRows := Equiv.refl _

omit [Fintype P] in
/-- Restoring a receiver's proposal gives the original layout, cells and
assignment at the chosen team. -/
theorem routedReportProposals_key (z : ownerRows) (u : Fin (R+1)) :
    let before := (routedReportProposals ar N cell owners slot label charts home bodies supplied wires).symm z
    (⟨_,_,before.2 u⟩ : (l : ReportLayout) × (cs : List (ReportCell l)) × ReportAssignments cs) =
      ⟨charts u,(received(z.1.val)).cells u,z.2 u⟩ := rfl

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI

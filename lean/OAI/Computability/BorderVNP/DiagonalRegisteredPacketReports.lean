import OAI.Computability.BorderVNP.DiagonalRegisteredRoutedEnds
import OAI.Computability.BorderVNP.DiagonalRoutedSourceReports

/-! # The original reported source at its registered owner type -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing CellMacro.Generator BorderVNP.Cube Physical Physical.NativeAssignments
open DiagonalTallyCellReports ReportDirectory

variable {D R sites : ℕ} {P : Type} {bits : P → ℕ} {a : CubeArena.Layout}
    {N : Network D P bits} {cell : N.Site → Fin a.cells}
    {registered resident : (Packet a.n a.header.d a.header.blocks → Selector a.n a.K a.h) → Fin a.header.d → Fin (R+1)}
    {slot : LiveBit N cell ↪ Slot a.n a.header.d a.header.blocks (a.h*a.b)}
    {label : Fin a.cells → Label (a.n+1) a.header.d}
    {charts : Fin (R+1) → ReportLayout} {home : Fin sites → Fin a.cells} {bundle : Fin sites → ReportBundle}
    {supply width : ℕ → ℕ} {q : NativeAssignments.Routed (b:=a.b) (s:=a.s) resident} {u : Fin (R+1)}
    {localChart : ReportLayout} {cells : List (ReportCell localChart)} {outcome : Fin sites → Prop}

local notation3 (prettyPrint := false) "source(" owner ")" =>
  routedSourceReports a N cell owner slot label charts home bundle supply width

/-- Reindex the same accepted physical route, the submitted and canonical
rows, and the original observations when the registered owner is identified
with the resident owner. The entire selector survives this change. -/
theorem SameReportCells.atRegisteredSource (same : SameReportCells cells ((source(resident)).cells q u))
    (accepted : (source(resident)).pins q)
    (original : ∀ j, (∃ c ∈ (source(resident)).cells q u, c.number=(home j).val) → outcome j)
    (names : registered=resident) :
    let packet := q.atRegisteredOwner names
    (source(registered)).pins packet ∧
      SameReportCells cells ((source(registered)).cells packet u) ∧
      (source(registered)).cells packet u=(source(resident)).cells q u ∧
      (∀ j, (∃ c ∈ (source(registered)).cells packet u, c.number=(home j).val) → outcome j) ∧
      packet.1=q.1 := by
  subst registered
  exact ⟨accepted,same,rfl,original,rfl⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI

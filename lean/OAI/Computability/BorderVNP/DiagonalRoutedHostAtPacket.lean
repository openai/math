import OAI.Computability.BorderVNP.DiagonalRoutedSourceReports

/-! # Original deliveries on cell rows selected by equal labels -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing CellMacro.Generator BorderVNP.Cube Physical Physical.NativeAssignments
open DiagonalTallyCellReports ReportDirectory

/-- Every delivered original on the observed owner rows is delivered for the
same routed selector in the issued packet's matching cell rows. -/
theorem hostedAtPacketLabel {a : CubeArena.Layout} {R sites team : ℕ}
    {owner : (Packet a.n a.header.d a.header.blocks → Selector a.n a.K a.h) → Fin a.header.d → Fin (R+1)}
    {resident packet : Fin a.cells → Label (a.n+1) a.header.d}
    {q : NativeAssignments.Routed (b:=a.b) (s:=a.s) owner} {chart : ReportLayout}
    {home : Fin sites → Fin a.cells} {bundle : Fin sites → ReportBundle}
    {bank supplied widths : ℕ → ℕ} {digits : ℕ → Fin chart.gadgets → Fin chart.countWidth → Bool}
    {result : Fin sites → Prop}
    (physical : ∀ j : Fin sites,
      (∃ c ∈ sourceCells chart home bundle team (routedOwnerWord a owner resident q) bank supplied widths digits,
        c.number=(home j).val) → result j)
    (names : packet=resident) :
    ∀ j : Fin sites,
      (∃ c ∈ sourceCells chart home bundle team (routedOwnerWord a owner packet q) bank supplied widths digits,
        c.number=(home j).val) → result j := by
  subst packet
  exact physical

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI

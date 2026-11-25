import OAI.Computability.BorderVNP.DiagonalObservedDispatchReportRows
import OAI.Computability.BorderVNP.DiagonalRoutedHostAtPacket

/-! # The complete original report scan on the labels of the signed packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM ScheduleClock SignedTaskArena DiagonalTallyAllocation DiagonalTallyCellReports
open DiagonalTallyCellReports.ReportDirectory FiniteEvaluator FragmentRows TeamContraction
open BorderVNP.Cube Physical Physical.NativeAssignments Packing.RoutingOutputs Packing.BottomReports

variable {R sites ports w : ℕ} {t : SignedTaskArena.Layout} {u : Fin (R+1)}
    {address base : ℕ} {home : Fin sites → Fin t.cube.cells}
local notation3 (prettyPrint := false) "ctrl" => controlsBase address t.cube.cables t.cube.cells sites ports
local notation3 (prettyPrint := false) "chart" => reportLayout t.before t.after base ctrl
  t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop

/-- Transport all prepared and allocated report cells together along equality of
the registered and resident owner words at every numeric cell address. -/
theorem DispatchReportRows.atOwnerWords {resident packet : ℕ → ℕ}
    {pub : Arg → Word w} {control : Memory w} {payload original : Fin sites → ReportBundle}
    {digits : ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool}
    {axis : Fin (t.cube.n+1)} {description : ℕ} {prior after bank supply width : ℕ → ℕ}
    {samples : ℕ → Fin (chart).gadgets → Fin (chart).countWidth → Bool}
    (recorded : DispatchReportRows t u (ports:=ports) address base home pub control payload digits axis description
      prior after (sourceCells chart home original u.val resident bank supply width samples))
    (names : packet=resident) :
    DispatchReportRows t u (ports:=ports) address base home pub control payload digits axis description
      prior after (sourceCells chart home original u.val packet bank supply width samples) := by
  subst packet
  exact recorded


/-- Retain both preparations, allocations, tail widths and supplemental words
on the full list of original cells when the packet names its resident labels. -/
theorem DispatchReportRows.atPacketLabel
    {owner : (Packet t.cube.n t.cube.header.d t.cube.header.blocks → Selector t.cube.n t.cube.K t.cube.h) →
      Fin t.cube.header.d → Fin (R+1)}
    {resident packet : Fin t.cube.cells → Label (t.cube.n+1) t.cube.header.d}
    {q : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owner}
    {pub : Arg → Word w} {control : Memory w} {payload original : Fin sites → ReportBundle}
    {digits : ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool}
    {axis : Fin (t.cube.n+1)} {description : ℕ} {prior after bank supply width : ℕ → ℕ}
    {samples : ℕ → Fin (chart).gadgets → Fin (chart).countWidth → Bool}
    (recorded : DispatchReportRows t u (ports:=ports) address base home pub control payload digits axis description
      prior after (sourceCells chart home original u.val (routedOwnerWord t.cube owner resident q) bank supply width samples))
    (names : packet=resident) :
    DispatchReportRows t u (ports:=ports) address base home pub control payload digits axis description
      prior after (sourceCells chart home original u.val (routedOwnerWord t.cube owner packet q) bank supply width samples) := by
  subst packet
  exact recorded

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.DiagonalReceivedReportLayoutCast
import OAI.Computability.BorderVNP.CubeRouteDataLayouts

/-! # The physical cell allocation after reading the installed frame register -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

namespace Cube.Physical.NativeAssignments.ReceivedRows

open DiagonalTallyCellReports DiagonalTallyAllocation RoutingISA RoutingISA.SignedTaskArena

variable (sa : SignedTaskArena.Layout) (control fieldWidth bodyCap : ℕ) {before after : ℕ}
local notation3 (prettyPrint := false) "chart" j =>
  reportLayout sa.before sa.after j control sa.p.parameters fieldWidth bodyCap sa.cube.stop

/-- Changing the spelling of the frame in both the public cell writer and the
report chart preserves the selected allocation with its original cursor. -/
theorem allocationAtFrame (rc : ReceivedRows (fun _ : Fin sa.cube.teams => chart before) sa.cube.cells)
    (installed : before=after) (t : Fin sa.cube.teams)
    (bankControl : ℕ) (axis : Fin (sa.cube.n+1)) {cursor : ReportCursor}
    (allocation : ReportAllocation sa.before sa.after (sa.cube.cellWriter before bankControl axis)
      (chart before) (rc.cells t) cursor) :
    ReportAllocation sa.before sa.after (sa.cube.cellWriter after bankControl axis)
      (chart after) ((rc.atLayout (l' := chart after) (congrArg (fun j => chart j) installed)).cells t) cursor :=
  match installed with
  | rfl => allocation

/-- The reindexed physical roster contains the same marked parameters and
binary places as the installed source rows. -/
theorem marksAtFrame (rc : ReceivedRows (fun _ : Fin sa.cube.teams => chart before) sa.cube.cells)
    (installed : before=after) (t : Fin sa.cube.teams) {w : ℕ}
    (marks : ∀ c ∈ rc.cells t, ∀ b ∈ c.bundles, ∀ g ∈ b.positions, g.parameter < 2^w ∧ g.place < w) :
    ∀ c ∈ (rc.atLayout (l' := chart after) (congrArg (fun j => chart j) installed)).cells t,
      ∀ b ∈ c.bundles, ∀ g ∈ b.positions, g.parameter < 2^w ∧ g.place < w :=
  match installed with
  | rfl => marks

end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI

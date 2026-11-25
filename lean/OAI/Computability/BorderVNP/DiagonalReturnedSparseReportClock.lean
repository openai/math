import OAI.Computability.BorderVNP.DiagonalSparsePreparedReports
import OAI.Computability.BorderVNP.DiagonalVisitedReportWidths

/-! # Transport the actually returned report source to the native post-scan roster -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM BorderVNP.Cube Cube.Physical Cube.TeamRowClock Cube.TeamRowSources
open DiagonalTallyCellReports DiagonalTallyCellReports.ReportDirectory TypedTaskBuilder

variable {Site E I P A : Type} [Fintype P] {w : ℕ} {a : CubeArena.Layout}
    {D : LengthDeclaration a.n a.header.d} {label : Fin a.cells → Label (a.n+1) a.header.d}
    {recv : A → Fin a.cells} {assigned : ℕ → ℕ}
    {r description p d R H B : ℕ} {team : Fin (r+1)} {pub : Arg → Word w} {m : Memory w}
    {src : SparseCallInput pub m} {f : FragmentRows.Layout} {bank : ℕ → ℕ} {l : CellControlRows.Layout} {mem : ℕ → ℕ}

variable {inputs : A → ℕ}
    (S : SparseReportSources Site E I P a D label recv inputs assigned team.val description p d R H B src f bank l mem)

local notation "owner" => scheduledCellOwner a D label assigned

/-- Recover an original native roster on the very same fields used in the
report charge, and identify its compact array with the private report return. -/
theorem SparseReportSources.LocalReadback.returnedRoster {arena : SignedTaskArena.Layout}
    (p : ℕ → CellPacket.Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record)
    (submitted : ℕ → SparseExterior.Owned) {L : ReportLayout} (atCell : ℕ → ReportCell L)
    {cs : List (ReportCell L)} {q : ReportCursor} {buf : Memory w} {mac : TeamOpcode.Macros w 8} {reg : Bank w}
    (rawSeed : PreparedReportInput pub buf cs q description) (ret : Returns prepareCellReports pub mac reg buf)
    (ordered : cs=visitedReportRows l mem atCell)
    (roster : ProducedRoster arena l mem p geom extra src)
    (seed : PreparedReportInput pub buf (S.reportRows (team:=team)) q description) :
    let selected := fun c : ℕ => (atCell c).withTape (rawSeed.returnedTape ret) (returnedTapePosition l mem cs c)
    S.LocalReadback (team:=team) geom p extra submitted (fun c => selected c.val) cs
        (((List.range l.cells).filter (fun c => decide (l.owner mem c=l.team))).map selected) →
      ProducedRoster arena l mem S.places S.geometry S.extra src ∧
      PreparedReportInput pub buf (S.reportRows (team:=team)) q description ∧
      S.LocalReadback (team:=team) geom p extra submitted (fun c => selected c.val) cs
        ((assignedReportReturnEquiv rawSeed mac reg).symm ret).val := by
  intro selected source
  have actual := (visitedReportRows_scan l mem selected).symm.trans (rawSeed.returnedVisitedRows l mem atCell ordered ret)
  refine ⟨?_,seed,?_⟩
  · rw [source.placedEq,source.geometryEq,source.extraEq]
    exact roster
  · rw [←actual]
    exact source

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI

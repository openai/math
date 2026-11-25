import OAI.Computability.BorderVNP.RoutingISASparseReportSources

/-! # Charged subtotal records in the positive branch's actual compact task order -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM BorderVNP.Cube Cube.Physical Cube.TeamRowClock Cube.TeamRowSources
open Crossing Packing.CellAddresses Packing.Directory DiagonalTallyCellReports
open Diagonal.ExternalSew.Fragments CellPacket CellSparse CellSparse.Packet CellSparse.Packet.Source
open CellPacketGeometry BorderVNP.FiniteEvaluator.OpenSuffix

variable {Site E I A P : Type} [Fintype P] {w : ℕ}
    {a : CubeArena.Layout} {D : LengthDeclaration a.n a.header.d} {label : Fin a.cells → Label (a.n+1) a.header.d}
    {recv : A → Fin a.cells} {incoming : A → ℕ} {pub : Arg → Word w}
    {assigned : ℕ → ℕ} {r description p d R H B : ℕ} {team : Fin (r+1)}
    {m : Memory w} {src : SparseCallInput pub m} {f : FragmentRows.Layout} {bank : ℕ → ℕ}
    {l : CellControlRows.Layout} {mem : ℕ → ℕ}
    (S : SparseReportSources Site E I P a D label recv incoming assigned team.val description p d R H B src f bank l mem)

/-- The two tally scans use the published count fields and the original
power slots owned by this team, on its native compact report array. -/
theorem SparseReportSources.finish_sizes :
    S.reportRows.length*(S.layout.gadgets+S.layout.gadgets*S.layout.countWidth) ≤ 2^p+2^d ∧
      teamWeighted S.reportRows ≤ R*(H*B) := by
  let owner := scheduledCellOwner a D label assigned
  let order := SparseExterior.programOrder l mem owner team.val S.cellCount S.teamID S.owners
  have loads := S.geometryCounts owner team.val
  have count := count_public_capacity owner team.val order S.layout (fun c => S.places c.val) S.reportCount S.digits loads.1
  have size : S.reportRows.length=l.before mem l.cells := List.length_ofFn
  have cost := owned_use_le owner team.val (fun c => (S.reports c).bundles) S.original
  have total := report_sum owner team.val order S.reports (fun c => weightedCopies c.bundles)
  change teamWeighted S.reportRows = _ at total
  exact ⟨size ▸ count.trans (Nat.le_add_right ..),total.trans_le cost⟩

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI

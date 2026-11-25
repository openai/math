import OAI.Computability.BorderVNP.DiagonalSignedHostReportBody
import OAI.Computability.BorderVNP.DiagonalPositiveCoreReceived
import OAI.Computability.BorderVNP.CellPacketGeometrySignedPublished
import OAI.Computability.BorderVNP.CellPacketSupplementalProducerRows

/-! # The receiving team's genuine original boxes on its signed sparse report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalTallyCellReports CellSparse.Packet.Source
open RoutingISA.TypedTaskBuilder RoutingISA.SignedTaskArena FiniteEvaluator CellPacketGeometry.SiteWords

/-- Convert the signed report's actual received bundle array and the original
geometry's owner map to the opaque-byte premise at all reached global cell
addresses. The sample value of the report does not affect this implication. -/
theorem ReceivedRows.reported_originals {w description T J ctl : ℕ} (a : SignedTaskArena.Layout)
    {layouts : Fin T → ReportLayout} (R : ReceivedRows layouts a.cube.cells) (u : Fin T)
    (scan : CellControlRows.Layout) (raw : ℕ → ℕ) (count : scan.cells=a.cube.cells)
    (size : scan.before raw scan.cells=(R.cells u).length)
    (ordinal : ∀ i : Fin (R.cells u).length, ((R.cells u).get i).number=globalCell scan.toLayout raw i.val)
    (home : Fin J → Fin a.cube.cells) (source : Fin J → ReportBundle)
    (roster : ∀ i : Fin (R.cells u).length,
      ((R.cells u).get i).bundles=(Packing.BundleDirectory.sourceRows home (R.order ⟨u,i⟩).val).map source)
    {Tag : Type} (G : Directory Tag (Fin J) (a.cube.cells+1))
    (originals : ∀ c : Fin a.cube.cells, ∀ j, Sum.inr j∈G.cellBoxes c.castSucc → home j=c)
    {pub : Arg → Word w} {entry : Memory w} {mac : TeamOpcode.Macros w 8} {regs : RoutingISA.Bank w}
    (H : OpenSuffix.Inputs) (ready : OpenSuffix.Ready H (pub 0).val (readings entry) w)
    (placed : OpenSuffix.Placement H a.cube a.before (pub 0).val (readings entry))
    (first : (pub 0).val+112≤a.cube.header.header) (opened : Returns OpenSuffix.code pub mac regs entry)
    {axis : Fin (a.cube.n+1)} {q : ReportCursor}
    (alloc : ReportAllocation a.before a.after (a.cube.cellWriter (pub 0).val ctl axis) (layouts u) (R.cells u) q)
    (seed : PreparedReportInput pub opened.val.2.2 (R.cells u) q description)
    (run : Returns prepareCellReports pub mac opened.val.2.1 opened.val.2.2)
    (intervals : SiteIntervals (R.cells u) description a.cube.cellStride)
    (hostImage : ∀ j, (∃ c∈R.cells u,c.number=(home j).val) →
      (source j).delivered (layouts u) description (OpenSuffix.hostImage (pub 0).val (readings entry)) ∧
        (source j).SiteRoom (layouts u) w description) :
    ∀ c : Fin a.cube.cells, scan.owner raw c.val=scan.team → ∀ j, Sum.inr j∈G.cellBoxes c.castSucc →
      Delivered (description:=description) (readings run.val.2.2) (source j).header.siteSlot (layouts u).fieldWidth (source j).factors := by
  intro c mine j selected
  have below : c.val<scan.cells := by rw [count]; exact c.isLt
  let i : Fin (R.cells u).length := ⟨scan.before raw c.val,(scan.toLayout.before_strict raw below mine).trans_eq size⟩
  have localCell : R.order ⟨u,i⟩=c := by
    apply Fin.ext
    exact (R.number u i).symm.trans ((ordinal i).trans (global_at scan.toLayout raw below mine))
  have owner := originals c j selected
  have present : source j∈((R.cells u).get i).bundles := by
    rw [roster i,localCell]
    exact List.mem_map.mpr ⟨j,Packing.BundleDirectory.mem_sourceRows.mpr (congrArg Fin.val owner),rfl⟩
  obtain ⟨word,room⟩ := hostImage j ⟨(R.cells u).get i,List.get_mem ..,
    (R.number u i).trans ((congrArg Fin.val localCell).trans (congrArg Fin.val owner).symm)⟩
  exact a.host_to_report_body H ready placed first opened alloc seed run intervals i (source j) present word room

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI

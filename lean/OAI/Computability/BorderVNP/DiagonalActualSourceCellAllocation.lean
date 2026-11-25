import OAI.Computability.BorderVNP.DiagonalSourceReceivedRows
import OAI.Computability.BorderVNP.DiagonalSignedReportEntry

/-! # Allocation of the original signed report rows in the installed cell banks -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

namespace RoutingISA.SignedTaskArena

open Packing BundleDirectory DiagonalTallyAllocation DiagonalTallyCellReports ReportDirectory
open private sourceLocalOrder from OAI.Computability.BorderVNP.DiagonalSourceReceivedRows

variable (t : Layout) {frame control bundles : ℕ}
    (home : Fin bundles → Fin t.cube.cells) (source : Fin bundles → ReportBundle)
    (team : Fin t.cube.cells → Fin t.cube.teams) (who : ℕ → ℕ)
    (assigned : ∀ c : Fin t.cube.cells, who c.val=(team c).val) (supply privateWidth : ℕ → ℕ)
    (digits : ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool)
local notation "chart" => reportLayout t.before t.after frame control t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
local notation "bank" => fun c => t.cube.cellBank+c*t.cube.cellStride

include assigned in
/-- The stable original-bundle grouping fits the physical report allocation on
each selected team, including a team with an empty ownership fiber. -/
theorem Layout.sourceCellsAllocation (u : Fin t.cube.teams) (axis : Fin (t.cube.n+1))
    (frameBefore : frame+96 ≤ t.cube.cellBank) (cells : t.cube.cells ≤ t.p.report.cells)
    (bundlesFit : bundles ≤ t.p.report.bundles)
    (receive : ∀ c : Fin t.cube.cells, supply c.val+
      (t.p.report.gadgets*t.p.report.countWidth+weightedCopies ((sourceRows home c.val).map source)) ≤ t.cube.cellStride)
    (supp : ∀ c : Fin t.cube.cells, supplementWords ((sourceRows home c.val).map source) ≤ t.p.report.supplementStride)
    (marks : ∀ j, (source j).positions.length ≤ t.p.report.marked)
    (expanded : (∑ j, (source j).useCount) ≤ t.p.report.uses) :
    ReportAllocation t.before t.after (t.cube.cellWriter frame control axis) chart
      (sourceCells chart home source u.val who bank supply privateWidth digits) t.after.reportCursor := by
  let cs := sourceCells chart home source u.val who bank supply privateWidth digits
  let charts := fun _ : Fin t.cube.teams => chart
  let ordinal := sourceLocalOrder charts home source team who assigned bank supply privateWidth (fun _ => digits) u
  let rc := receivedSourceRows charts home source team who assigned bank supply privateWidth (fun _ => digits)
  have number (i : Fin cs.length) : cs[i].number=(ordinal i).val.val := rc.number u i
  have grouped (i : Fin cs.length) : cs[i].bundles=(sourceRows home (ordinal i).val.val).map source := by
    rw [←number i]
    have member : cs[i] ∈ cs := List.getElem_mem i.isLt
    obtain ⟨c,_,eq⟩ := List.mem_map.mp member
    exact (congrArg (fun row : ReportCell chart => row.bundles=(sourceRows home row.number).map source) eq).mp rfl
  have after : t.before.limit ≤ t.after.start := by
    change t.before.limit ≤ t.before.limit+3*t.cube.cells+7*t.cube.cells+
      t.p.scratchStride*t.cube.cells+t.p.burstStride*t.cube.cells
    omega
  have past : t.cube.stop ≤ t.before.start := by
    apply LE.le.trans _ t.constants_le_before
    unfold CubeConstants.arenaEnd CubeConstants.idBase
    omega
  apply ReportAllocation.of_sourceRows_le t.before t.after (t.cube.cellWriter frame control axis)
    frame control t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop cs home team u ordinal source
    number grouped le_rfl cells rfl frameBefore past after _ supp bundlesFit marks expanded
  intro c hc
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
  exact ⟨rfl,receive ⟨j,List.mem_range.mp (List.mem_filter.mp hj).1⟩⟩

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI

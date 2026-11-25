import OAI.Computability.BorderVNP.FragmentTaskGeometryPublication
import OAI.Computability.BorderVNP.FragmentTaskPublishedRanks
import OAI.Computability.BorderVNP.FragmentTaskReportWidths

/-! # Physical task-source geometry of every returned native report tape -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA RoutingISA.FragmentRows RoutingISA.SignedTaskArena
open Packing Packing.RoutingOutputs GeometryAdvice DiagonalTallyAllocation

variable {a : SignedTaskArena.Layout} {w : ℕ} {pub : Arg → Word w} {m : Memory w}
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor} {banks : CellBanks.Layout}
    {description fresh profile gates outputs bits J A descriptorColumn : ℕ}

local notation "frame" => readings pub 0
local notation "origin" => Allocation.dest fresh profile gates outputs bits
local notation "offsets" => Bases.ends (bases origin a.cube.cables a.cube.cells J)
local notation "ctl" => controlsBase origin a.cube.cables a.cube.cells J A
local notation "dir" => GeometryDirectories.mk a.p.sorted a.p.padded a.p.stops a.p.bundlePayload a.p.bundleInverse

/-- At each tape's genuine native report return, the geometry columns,
descriptor inverse and report extent publication give the exact task source
certificate used by the subsequent fragment and task builder. -/
theorem reportReturn_task_geometry
    (alloc : ReportAllocation a.before a.after banks l cs q) (seed : PreparedReportInput pub m cs q description)
    (mac : TeamOpcode.Macros w 8) (reg : Bank w) (tape : ReportTape cs)
    (start : frame+112 ≤ fresh) (cap : a.cube.cells ≤ a.p.report.cells)
    (total : a.cube.cables*3+(RoutingOutputs.count a.cube.cables a.cube.cells J A+
      ((a.cube.cells+(J+a.cube.cells))+(37+(descriptorColumn+2*a.p.padded)))) ≤ outputs)
    (cube : a.cube.header.header=Allocation.stop fresh profile gates outputs bits w)
    (sorted : a.p.sorted=ctl+37+descriptorColumn)
    (ranks : (dir).MarkerBounds a.cube.cells (readings m))
    (frameAt : l.frame=frame) (bank : banks.bankStart=a.cube.cellBank)
    (cells : banks.cells=a.cube.cells) (stride : banks.stride=a.cube.cellStride)
    (counts : ∀ r∈cs, readings m (offsets+2*a.cube.cables+r.number)=r.supplied)
    (full : ∀ c : Fin banks.cells, readings m (offsets+2*a.cube.cables+c.val)≤banks.stride)
    (blank : ∀ c : Fin banks.cells, readings m (a.before.tailWidths+c.val)=0) :
    a.SparsePlacement frame ctl ∧ TaskSourceGeometry a frame offsets ctl (readings (reportReturnEquiv seed mac reg tape).val.2.2) := by
  have low : frame+112 ≤ origin := by dsimp only [Allocation.dest,Allocation.temp]; omega
  have endGeom : origin+outputs ≤ a.cube.header.header := by
    rw [cube]; dsimp only [Allocation.stop,Allocation.packed,Allocation.dense]; omega
  have hBank := a.open_table_order.1
  have ends : frame+112 ≤ offsets ∧ offsets+2*a.cube.cables+a.cube.cells ≤ ctl ∧
      ctl+37+descriptorColumn+2*a.p.padded ≤ origin+outputs := by
    dsimp only [controlsBase,bases,RoutingOutputs.count] at total ⊢
    omega
  have r := alloc.reportReturn_markerBounds seed mac reg tape dir ranks le_rfl
    (by change l.frame+35 < a.p.sorted+a.p.padded; omega)
    (by change a.p.sorted+2*a.p.padded ≤ banks.bankStart; omega)
  have ext := reportReturnEquiv_task_extents alloc seed mac reg tape offsets cells stride
    (by omega) (by omega) counts full blank
  exact task_geometry_of_publication a _ start cap total cube sorted r.markers r.ranks ext

/-- At each tape's genuine native report return, the geometry columns,
descriptor inverse and report extent publication give the exact task source
certificate used by the subsequent fragment and task builder. -/
theorem reportReturn_task_geometry_owned
    (alloc : ReportAllocation a.before a.after banks l cs q) (seed : PreparedReportInput pub m cs q description)
    (mac : TeamOpcode.Macros w 8) (reg : Bank w) (tape : ReportTape cs)
    (start : frame+112 ≤ fresh) (cap : a.cube.cells ≤ a.p.report.cells)
    (total : a.cube.cables*3+(RoutingOutputs.count a.cube.cables a.cube.cells J A+
      ((a.cube.cells+(J+a.cube.cells))+(37+(descriptorColumn+2*a.p.padded)))) ≤ outputs)
    (cube : a.cube.header.header=Allocation.stop fresh profile gates outputs bits w)
    (sorted : a.p.sorted=ctl+37+descriptorColumn)
    (ranks : (dir).MarkerBounds a.cube.cells (readings m))
    (frameAt : l.frame=frame) (bank : banks.bankStart=a.cube.cellBank)
    (stride : banks.stride=a.cube.cellStride)
    (counts : ∀ r∈cs, readings m (offsets+2*a.cube.cables+r.number)=r.supplied)
    (team : ℕ) (roster : ∀ c<a.cube.cells, readings m (a.cube.hostDirectory+2*c)=team → ∃ r∈cs,r.number=c) :
    a.SparsePlacement frame ctl ∧ TaskSourceGeometry a frame offsets ctl (readings (reportReturnEquiv seed mac reg tape).val.2.2) (some team) := by
  have low : frame+112 ≤ origin := by dsimp only [Allocation.dest,Allocation.temp]; omega
  have endGeom : origin+outputs ≤ a.cube.header.header := by
    rw [cube]; dsimp only [Allocation.stop,Allocation.packed,Allocation.dense]; omega
  have hBank := a.open_table_order.1
  have ends : frame+112 ≤ offsets ∧ offsets+2*a.cube.cables+a.cube.cells ≤ ctl ∧
      ctl+37+descriptorColumn+2*a.p.padded ≤ origin+outputs := by
    dsimp only [controlsBase,bases,RoutingOutputs.count] at total ⊢
    omega
  have r := alloc.reportReturn_markerBounds seed mac reg tape dir ranks le_rfl
    (by change l.frame+35 < a.p.sorted+a.p.padded; omega)
    (by change a.p.sorted+2*a.p.padded ≤ banks.bankStart; omega)
  obtain ⟨_,_,_,_,_,_,power,powers,group,owner,pairs,hosts,_⟩ := a.cube.group_order
  have first := a.cube.group_order.1
  have hostEnd := a.open_table_order.2.1
  have ext := reportReturnEquiv_owned_extents alloc seed mac reg tape offsets team stride (by omega) (by omega)
    (by omega) (by omega) counts roster
  exact task_geometry_of_publication_at a _ (some team) start cap total cube sorted r.markers r.ranks ext

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsDirectory
import OAI.Computability.BorderVNP.DiagonalSignedPhysicalReportData
import OAI.Computability.BorderVNP.FragmentTaskReportPublication

/-! # The report extent bound on the native owner's actual cell directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports.ReportDirectory

open VPVNP.BurstRAM Packing RoutingISA TypedTaskBuilder
open CellControlRows

/-- Reading the completed cell-control publisher, every reported row has
the stated supply and every owned global cell has an actual report row. -/
theorem directoryCells_published_inputs (d : BundleDirectory.Layout) (rows : CellControlRows.Layout) (l : ReportLayout)
    (home : Fin d.bundles → Fin d.cells) (source : Fin d.bundles → ReportBundle)
    (m : ℕ → ℕ) (counts : ℕ → Fin l.gadgets → Fin l.countWidth → Bool)
    {w : ℕ} (room : rows.Room w) :
    let cs := directoryCells d rows l home source m counts
    (∀ r∈cs, rows.published m (rows.offsets+2*rows.cables+r.number)=r.supplied) ∧
    ∀ c<rows.cells, rows.published m (rows.banks+2*c)=rows.team → ∃ r∈cs,r.number=c := by
  intro cs
  have kept (c : ℕ) (hc : c<rows.cells) (z : ℕ) (hz : rows.inputs c z) : rows.published m z=m z := by
    have protectedWord := room.inputApart c hc z hz
    have diff : z≠rows.frame+90 := fun eq => protectedWord (.inr (.inr eq))
    rw [CellControlRows.Layout.published,Function.update_of_ne diff, image_outside rows m le_rfl protectedWord]
  constructor
  · intro r hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    let c := globalCell rows.toLayout m j.val
    have hc : c<rows.cells := (global_spec rows.toLayout m j.isLt).1
    exact kept c hc _ (.inr (.inr (.inl rfl)))
  · intro c hc own
    have orig : rows.toLayout.owner m c=rows.team := (kept c hc _ (.inl rfl)).symm.trans own
    let i : Fin (rows.before m rows.cells) := ⟨rows.before m c,rows.toLayout.before_strict m hc orig⟩
    refine ⟨directoryCell d rows l home source m counts (globalCell rows.toLayout m i),List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
    exact global_at rows.toLayout m hc orig

end DiagonalTallyCellReports.ReportDirectory

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM Packing FiniteEvaluator BorderVNP.Cube DiagonalTallyAllocation DiagonalTallyCellReports
open ReportDirectory TeamContraction.JointHeader DiagonalResidueRAM Crossing Packing.Inherited Packing.CellAddresses CellSparse
open RoutingISA.Evaluator

variable (t : Layout) {w team frame offsets control live ports bundles b : ℕ}
variable (owner : Fin bundles → Fin t.cube.cells) (source : Fin bundles → ReportBundle)
variable (counts : ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool)
variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {mem : Memory w}

local notation "r" => reportLayout t.before t.after frame control t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
local notation "d" => t.bundleLayout frame control bundles
local notation "rows" => t.controlRows team frame offsets control live ports
local notation "H" => t.openInputs team frame offsets control live ports bundles b owner (ReportBundle.header ∘ source)
local notation "host" => OpenSuffix.hostImage frame (readings mem)
local notation "cs" => directoryCells d rows r owner source (grouped d owner source host) counts

/-- Recover the complete owned roster and every supplied width from the
actual control return on which the next report traversal begins. -/
theorem Layout.signedReport_owned_inputs (ready : OpenSuffix.Ready H (pub 0).val (readings mem) w)
    (base : (pub 0).val=frame) (ret : Returns SignedPrep.controls pub mac s mem) :
    (∀ r₀∈cs, readings ret.val.2.2 (offsets+2*t.cube.cables+r₀.number)=r₀.supplied) ∧
    ∀ c<t.cube.cells, readings ret.val.2.2 (t.cube.hostDirectory+2*c)=team →
      ∃ r₀∈cs,r₀.number=c := by
  have image := (OpenSuffix.control_return_facts H ready ret).2.2.2
  change readings ret.val.2.2=(rows).published (grouped d owner source (OpenSuffix.hostImage (pub 0).val (readings mem))) at image
  rw [base] at image
  rw [image]
  exact directoryCells_published_inputs d rows r owner source _ counts ready.controls

section Returned

open GeometryAdvice Packing.RoutingOutputs FragmentRows
variable {fresh profile gates outputs bitWidth descriptorColumn : ℕ}
local notation3 (prettyPrint := false) "head₀" => readings pub 0
local notation3 (prettyPrint := false) "origin₀" => Allocation.dest fresh profile gates outputs bitWidth
local notation3 (prettyPrint := false) "tables₀" => bases origin₀ t.cube.cables t.cube.cells bundles
local notation3 (prettyPrint := false) "ctl₀" => controlsBase origin₀ t.cube.cables t.cube.cells bundles ports
local notation3 (prettyPrint := false) "layout₀" => reportLayout t.before t.after head₀ ctl₀ t.p.parameters
  t.p.siteWidth t.p.bodyCap t.cube.stop
local notation3 (prettyPrint := false) "bundle₀" => t.bundleLayout head₀ ctl₀ bundles
local notation3 (prettyPrint := false) "rows₀" => t.controlRows team head₀ (tables₀).ends ctl₀ (tables₀).livePairs ports
local notation3 (prettyPrint := false) "prog₀" => t.openInputs team head₀ (tables₀).ends ctl₀ (tables₀).livePairs ports
  bundles b owner (ReportBundle.header ∘ source)
local notation3 (prettyPrint := false) "cs₀" => directoryCells bundle₀ rows₀ layout₀ owner source
  (grouped bundle₀ owner source (OpenSuffix.hostImage head₀ (readings mem))) counts

/-- Source geometry of an arbitrary returned report run following this
actual control return. The real owned directory supplies both the complete
roster and its widths before any report digits are consumed. -/
theorem Layout.signedReport_task_geometry (ready : OpenSuffix.Ready prog₀ head₀ (readings mem) w)
    (opened : Returns SignedPrep.controls pub mac s mem) {banks : CellBanks.Layout} {q : ReportCursor} {description : ℕ}
    (alloc : ReportAllocation t.before t.after banks layout₀ cs₀ q)
    (seed : PreparedReportInput pub opened.val.2.2 cs₀ q description)
    (report : Returns prepareCellReports pub mac opened.val.2.1 opened.val.2.2)
    (start : head₀+112 ≤ fresh) (cap : t.cube.cells ≤ t.p.report.cells)
    (total : t.cube.cables*3+(RoutingOutputs.count t.cube.cables t.cube.cells bundles ports+
      ((t.cube.cells+(bundles+t.cube.cells))+(37+(descriptorColumn+2*t.p.padded)))) ≤ outputs)
    (cube : t.cube.header.header=Allocation.stop fresh profile gates outputs bitWidth w)
    (sorted : t.p.sorted=ctl₀+37+descriptorColumn)
    (ranks : (GeometryDirectories.mk t.p.sorted t.p.padded t.p.stops t.p.bundlePayload t.p.bundleInverse).MarkerBounds
      t.cube.cells (readings opened.val.2.2))
    (bank : banks.bankStart=t.cube.cellBank) (stride : banks.stride=t.cube.cellStride) :
    t.SparsePlacement head₀ ctl₀ ∧ TaskSourceGeometry t head₀ (tables₀).ends ctl₀ (readings report.val.2.2) (some team) := by
  obtain ⟨supply,roster⟩ := t.signedReport_owned_inputs owner source counts ready rfl opened
  obtain ⟨tape,rfl⟩ := (reportReturnEquiv seed mac opened.val.2.1).surjective report
  exact reportReturn_task_geometry_owned alloc seed mac opened.val.2.1 tape start cap total cube sorted ranks rfl bank
    stride supply team roster

end Returned
end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI

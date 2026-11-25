import OAI.Computability.BorderVNP.DiagonalSignedReportSetup
import OAI.Computability.BorderVNP.DiagonalLocalReportSetup

/-! # Physical local report rows and the sparse continuation -/

namespace OAI
namespace Computability
namespace BorderVNP

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

/-- The returned controls supply a fitted report scan and the true allocation
before the private report digits or the sparse argument have been chosen. -/
theorem Layout.signedReportPreparation (axis : Fin (t.cube.n+1)) (description : ℕ)
    (ready : OpenSuffix.Ready H (pub 0).val (readings mem) w)
    (place : OpenSuffix.Placement H t.cube t.before frame (readings mem))
    (room : t.OpenRoom frame offsets control live ports bundles (2^b) w)
    (base : (pub 0).val=frame) (ctrlAt : readings mem (frame+92)=control)
    (inputs : readings mem (frame+44)=t.after.descriptors ∧ readings mem (frame+81)=t.cube.stop ∧
      readings mem (frame+95)=t.p.parameters)
    (ctl : ∀ i : Fin 37, readings mem (control+i.val)=t.controls i.val) (frameEnd : frame+112 ≤ control)
    (receive : ∀ c : Fin t.cube.cells, readings mem (offsets+2*t.cube.cables+c.val)+
      (t.p.report.gadgets*t.p.report.countWidth+weightedCopies ((BundleDirectory.sourceRows owner c.val).map source))
        ≤ t.cube.cellStride)
    (supp : ∀ c : Fin t.cube.cells, supplementWords ((BundleDirectory.sourceRows owner c.val).map source) ≤ t.p.report.supplementStride)
    (marks : ∀ j,(source j).positions.length ≤ t.p.report.marked)
    (expanded : (∑ j,(source j).useCount) ≤ t.p.report.uses)
    (delivered : ∀ j,(∃ c∈cs,(owner j).val=c.number) → (source j).delivered r description host ∧
      (source j).SiteRoom r w description)
    (intervals : SiteIntervals cs description t.cube.cellStride)
    (privateFit : ∀ c∈cs,c.privateWires+c.supplied+c.tailWidth<2^w)
    (widthFit : t.p.siteWidth ≤ w) (sourceFit : t.p.siteWidth+t.p.bodyCap<2^w)
    {u v k : ℕ} (endFit : t.endAddress w u v k<2^w)
    : ReportAllocation t.before t.after (t.cube.cellWriter frame control axis) r cs t.after.reportCursor ∧
      ∀ ret : Returns SignedPrep.controls pub mac s mem,
        PreparedReportInput pub ret.val.2.2 cs t.after.reportCursor description := by
  classical
  have alloc := t.signedDirectoryAllocation owner source place room axis counts receive supp marks expanded
  refine ⟨alloc,?_⟩
  intro ret
  obtain ⟨seed,controls⟩ := t.signedReportSeed owner source place room ctrlAt inputs ctl
  have controlBound := room.controlEnd.trans t.open_table_order.1
  have space : t.after.fresh<2^w ∧ t.dim<2^w := by
    unfold Layout.endAddress Layout.entry gateBase Layout.valuation Layout.tallyBits AfterTasks.localBase at endFit
    omega
  have image := (OpenSuffix.control_return_facts H ready ret).2.2.2
  change readings ret.val.2.2=(rows).published (grouped d owner source (OpenSuffix.hostImage (pub 0).val (readings mem))) at image
  rw [base] at image
  exact ReportDirectory.preparedInput_owned (banks:=t.cube.cellWriter frame control axis) (pre:=t.before) (post:=t.after)
    (l:=r) (q:=t.after.reportCursor) d rows owner source host counts (t.signedReportBindings room) base seed
    (room.controls_fit team) controls (by change control+28≤t.cube.cellBank; omega)
    (.inr (by change frame+96≤control; omega)) delivered widthFit space.2 sourceFit space.1
    alloc intervals privateFit image

/-- Construct the genuine per-team report directory immediately after its own
control scans. The original bundles and all received header widths determine
the cell list before any report digits or sparse calls have been sampled. -/
noncomputable def Layout.signedLocalReportData (axis : Fin (t.cube.n+1)) (description : ℕ)
    (ready : OpenSuffix.Ready H (pub 0).val (readings mem) w)
    (place : OpenSuffix.Placement H t.cube t.before frame (readings mem))
    (room : t.OpenRoom frame offsets control live ports bundles (2^b) w)
    (base : (pub 0).val=frame) (ctrlAt : readings mem (frame+92)=control)
    (inputs : readings mem (frame+44)=t.after.descriptors ∧ readings mem (frame+81)=t.cube.stop ∧
      readings mem (frame+95)=t.p.parameters)
    (ctl : ∀ i : Fin 37, readings mem (control+i.val)=t.controls i.val) (frameEnd : frame+112 ≤ control)
    (receive : ∀ c : Fin t.cube.cells, readings mem (offsets+2*t.cube.cables+c.val)+
      (t.p.report.gadgets*t.p.report.countWidth+weightedCopies ((BundleDirectory.sourceRows owner c.val).map source))
        ≤ t.cube.cellStride)
    (supp : ∀ c : Fin t.cube.cells, supplementWords ((BundleDirectory.sourceRows owner c.val).map source) ≤ t.p.report.supplementStride)
    (marks : ∀ j,(source j).positions.length ≤ t.p.report.marked)
    (expanded : (∑ j,(source j).useCount) ≤ t.p.report.uses)
    (delivered : ∀ j,(∃ c∈cs,(owner j).val=c.number) → (source j).delivered r description host ∧
      (source j).SiteRoom r w description)
    (intervals : SiteIntervals cs description t.cube.cellStride)
    (privateFit : ∀ c∈cs,c.privateWires+c.supplied+c.tailWidth<2^w)
    (widthFit : t.p.siteWidth ≤ w) (sourceFit : t.p.siteWidth+t.p.bodyCap<2^w)
    {u v k : ℕ} (endFit : t.endAddress w u v k<2^w)
    (arguments : ∀ (ret : Returns SignedPrep.controls pub mac s mem)
      (report : Returns prepareCellReports pub mac ret.val.2.1 ret.val.2.2),
      Nonempty (SignedPrep.ArgumentInput pub mac report.val.2.1 report.val.2.2)) :
    SignedPrep.LocalReportData pub mac s mem := by
  classical
  have prepared := (t.signedReportPreparation (mac:=mac) (s:=s) owner source counts axis description ready place room base ctrlAt inputs
    ctl frameEnd receive supp marks expanded delivered intervals privateFit widthFit sourceFit endFit).2
  exact ⟨r,cs,t.after.reportCursor,description,prepared,fun ret choices =>
    (arguments ret (assignedReportReturnEquiv (prepared ret) mac ret.val.2.1 choices)).some⟩

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI

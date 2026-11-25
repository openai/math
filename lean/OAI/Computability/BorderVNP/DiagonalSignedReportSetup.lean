import OAI.Computability.BorderVNP.DiagonalSignedReportEntry
import OAI.Computability.BorderVNP.RoutingISASignedReaderArena

/-! # The real signed report setup on each returning owned control path -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM Packing FiniteEvaluator BorderVNP.Cube DiagonalTallyAllocation DiagonalTallyCellReports
open ReportDirectory TeamContraction.JointHeader DiagonalResidueRAM Crossing Packing.Inherited Packing.CellAddresses CellSparse
open RoutingISA.Evaluator

variable {D ns ne np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
variable (N : Network D P bits) (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
    (portID : P ↪ Fin np) (siteOwner : Fin ns → ℕ) (state : N.Site → Site)
    (g : ∀ c, Fin (guessedSize N cell c) → Bool)
    (a : ∀ c, Fin (siteSize N cell c (fun v => (state v).size)) → Bool)
    (x : ∀ c, Fin (suppliedSize N cell c) → Bool)
    (bottom : ℕ → List BottomReports.Bundle) (observed : ℕ → List (Bool × Option ℕ))

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

/-- Any authentic return of the four control stages supplies the signed report
input for precisely its owned cells. The original site strings and private
sizes are checked only where the native traversal reads them. -/
theorem Layout.signedReportSetup (axis : Fin (t.cube.n+1)) (description : ℕ)
    (ret : Returns SignedPrep.controls pub mac s mem)
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
    {u v k : ℕ} (endFit : t.endAddress w u v k<2^w) :
    ReportSetup pub ret.val.2.2 t.after.reportCursor description
      (assigned N cell siteID edgeID portID siteOwner state g a x bottom observed cs) := by
  have returned := (OpenSuffix.control_return_facts H ready ret).2
  obtain ⟨seed,controls⟩ := t.signedReportSeed owner source place room ctrlAt inputs ctl
  have alloc := t.signedDirectoryAllocation owner source place room axis counts receive supp marks expanded
  have controlBound := room.controlEnd.trans t.open_table_order.1
  have space : t.after.fresh<2^w ∧ t.dim<2^w := by
    unfold Layout.endAddress Layout.entry gateBase Layout.valuation Layout.tallyBits AfterTasks.localBase at endFit
    omega
  have actual := setup_after_controls (banks:=t.cube.cellWriter frame control axis) (pre:=t.before) (post:=t.after) (l:=r) (q:=t.after.reportCursor) N cell siteID edgeID portID siteOwner state g a x bottom observed d rows owner source
    (2^b) description counts ret
  dsimp only at actual
  rw [base] at actual
  exact actual returned (t.signedReportBindings room) rfl seed (room.controls_fit team) controls
    (by change control+28 ≤ t.cube.cellBank; omega) (.inr (by change frame+96 ≤ control; omega))
    delivered widthFit space.2 sourceFit space.1 alloc intervals privateFit

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI

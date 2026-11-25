import OAI.Computability.BorderVNP.DiagonalLocalReportAllocation
import OAI.Computability.BorderVNP.DiagonalSameReportIntervals
import OAI.Computability.BorderVNP.DiagonalFrozenPaddingControls
import OAI.Computability.BorderVNP.DiagonalTallyGadgetReadback
import OAI.Computability.BorderVNP.RoutingISASignedPrepReportDirectory

/-! # Entering the native report traversal on one original control return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM DiagonalTallyCellReports ReportDirectory DiagonalTallyAllocation
open Evaluator FiniteEvaluator Packing.BottomReports DiagonalResidueRAM TeamContraction TeamContraction.JointHeader
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Padding.Banks

variable (task : Layout) {w team frame offsets ctl live ports bundles b : ℕ}
    (home : Fin bundles → Fin task.cube.cells) (payload : Fin bundles → ReportBundle)
    (digits : ℕ → Fin task.p.report.gadgets → Fin task.p.report.countWidth → Bool)
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {regs : Bank w} {mem : Memory w}

local notation3 (prettyPrint := false) "rep" => reportLayout task.before task.after frame ctl
  task.p.parameters task.p.siteWidth task.p.bodyCap task.cube.stop
local notation3 (prettyPrint := false) "file" => task.bundleLayout frame ctl bundles
local notation3 (prettyPrint := false) "rows" => task.controlRows team frame offsets ctl live ports
local notation3 (prettyPrint := false) "prog" => task.openInputs team frame offsets ctl live ports bundles b home
  (ReportBundle.header ∘ payload)
local notation3 (prettyPrint := false) "host" => OpenSuffix.hostImage frame (readings mem)
local notation3 (prettyPrint := false) "cs" => directoryCells file rows rep home payload (grouped file home payload host) digits

/-- The executable report's input follows from its original allocated directory,
the retained private literals and the returned host/group/control publication.
The verification of this state precedes every submitted sparse call. -/
theorem Layout.preparedOriginalReportOnReturn (axis : Fin (task.cube.n+1)) (description : ℕ)
    (r : Returns SignedPrep.controls pub mac regs mem)
    {profile : ℕ → ℕ} {supplied : Fin task.cube.cells → ℕ}
    (control : FrozenControlEntry task prog frame (pub 0).val ctl offsets w supplied profile (readings mem))
    (room : task.OpenRoom frame offsets ctl live ports bundles (2^b) w)
    {reserve axes symbols cap width raw : ℕ} {fields : PositiveFields reserve axes symbols cap task.cube.teams task.dim width}
    (header : HeaderSeed task fields pub raw team mem)
    (owner : Fin task.cube.header.d → ℕ) (demand : ℕ)
    (data : Data task.cube.n task.cube.header.d task.cube.header.blocks task.cube.b task.cube.h task.cube.K task.cube.s)
    (deck : CubePacket.WordPrepared (gadgetLookup task pub owner team demand data) task.id pub mem)
    (allocated : ReportAllocation task.before task.after (task.cube.cellWriter frame ctl axis) rep cs task.after.reportCursor)
    (literals : ∀ j,(∃ c∈cs,(home j).val=c.number) →
      (payload j).delivered rep description host ∧ (payload j).SiteRoom rep w description)
    (intervals : SiteIntervals cs description task.cube.cellStride)
    (privateFit : ∀ c∈cs,c.privateWires+c.supplied+c.tailWidth<2^w)
    (widthFit : task.p.siteWidth≤w) (sourceFit : task.p.siteWidth+task.p.bodyCap<2^w)
    {u v k : ℕ} (endFit : task.endAddress w u v k<2^w) :
    PreparedReportInput pub r.val.2.2 cs task.after.reportCursor description := by
  have returned := (OpenSuffix.control_return_facts prog control.ready r).2.2.2
  rw [control.frame] at returned
  have inputs := task.signedReportWords control.frame header deck rfl
  have apart := control.frameEnd
  obtain ⟨seed,settings⟩ := task.signedReportSeed home payload control.placement room control.controlWord inputs control.controls
  have ctrlTop := room.controlEnd.trans task.open_table_order.1
  have space : task.after.fresh<2^w ∧ task.dim<2^w := by
    unfold Layout.endAddress Layout.entry gateBase Layout.valuation Layout.tallyBits AfterTasks.localBase at endFit
    omega
  exact preparedInput_owned (description:=description) (pub:=pub) (m:=r.val.2.2) (l:=rep)
    (pre:=task.before) (post:=task.after) (banks:=task.cube.cellWriter frame ctl axis) (q:=task.after.reportCursor)
    file rows home payload host digits (task.signedReportBindings room) control.frame
    seed (room.controls_fit team) settings (by change ctl+28≤task.cube.cellBank; omega)
    (.inr (by change frame+96≤ctl; omega)) literals widthFit space.2 sourceFit space.1
    allocated intervals privateFit returned

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI

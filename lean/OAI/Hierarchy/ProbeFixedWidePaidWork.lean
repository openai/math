import OAI.Hierarchy.ProbeFixedWidePaidRun
import OAI.Hierarchy.ProbeFixedPaidOperandWork
import OAI.Hierarchy.ProtocolRAMCoreSpillWork
import OAI.Hierarchy.ProtocolRAMCalendarSliceWork

namespace OAI
/-! # Pricing the actual direct, mate, forest, spill and boundary slices -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StockCommit
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A))
local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "banks" => TerminalLayout.settlement page stock
local notation "src" => TerminalLayout.source page
local notation "tab" => TerminalLayout.table page
local notation "dst" => TerminalLayout.destination page
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "order" => wideRouteOrder h D k
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "route" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
  (directory).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "C" => v.wideSignedChart h width stock


def wideOperandCost := max v.paidOperandWork (spillOperandWork (publicStages v.W) k v.wideJobs)

def wideIssueCost (maxBroadcastBits : ℕ) := PaidWidths.issueWork v.wideOperandCost maxBroadcastBits

set_option maxHeartbeats 1000000 in
theorem wide_issue_work (maxBits : ℕ) (bank : Bank) (t : PaidWidths.Slice)
    (ht : t∈v.widePaidSlices h width maxBits) :
    (RepairHistogram.pair (t.columns bank (P).catalogue.rows)).work≤v.wideIssueCost maxBits := by
  let layout:=FeedLayout.atEvent («N»:=N) v.mesh A (v.nativeFormats P h width) (P).joint.initial width v.keepLimit
  let recipe:=routeBanks start cnt r
  have stage : N=publicStages v.W:=fixed_stage_count h v.W
  have fixed : v.paidOperandWork≤v.wideOperandCost:=le_max_left ..
  have routed : spillOperandWork N k v.wideJobs≤v.wideOperandCost:=by rw [stage];exact le_max_right ..
  let fmt:=v.nativeFormats P h width
  let feeds:=feedColumns («N»:=N) v.mesh A fmt (P).joint.initial width v.keepLimit
  let sink:=(P).catalogue.sink r banks src tab dst owners
  exact paid_issues_work v.mesh fmt feeds sink (P).catalogue.idBase (fun a=>(StripChart.header F s a).fieldTerm)
    (StripChart.id F s (P).catalogue) (v.nativeTrees P h width) (v.paidSpillPath P h width recipe route order)
    (v.paidFeedPath P h width route layout) maxBits v.wideOperandCost bank (by
    intro a _
    obtain ⟨direct,tree,source,mate⟩:=v.wide_paid_operand_work h width r banks src tab dst owners a
    have sp:=early_work (attempts:=v.wideJobs) recipe route v.sampler order
      (v.catalystPairOwners P h width) (v.catalystPairParity P h width)
    exact ⟨direct.trans fixed,fun mask target same=>⟨((mate mask target same).1).trans fixed,
      ((mate mask target same).2).trans fixed⟩,tree.trans fixed,source.trans fixed,sp.1.trans routed,sp.2.trans routed⟩
  ) (by
    intro b _ c _
    have same:=boundary_work (attempts:=v.wideJobs) route v.sampler (layout b)
      (v.catalystPairOwners P h width) (v.catalystPairParity P h width) c
    exact ⟨same.1.trans routed,same.2.trans routed⟩) t ht

theorem wide_paid_invoice (maxBits : ℕ) :
    let ss:=v.widePaidSlices h width maxBits
    let work:=v.wideIssueCost maxBits
    PaidWidths.clock (banks).width (P).catalogue.rows ss≤8+6*(P).catalogue.rows+7*ss.length+
      (ss.map PaidWidths.Slice.count).sum*(4*work+20) ∧
    (ss.map (fun t=>rowText (RepairHistogram.pair (t.columns (banks).width (P).catalogue.rows))+22)).sum≤
      ss.length*(33+4*work) :=
  Whole.Priced.Paid.archive_bill (v.widePaidSlices h width maxBits) (banks).width (P).catalogue.rows
    (v.wideIssueCost maxBits) (v.wide_issue_work h width maxBits (banks).width)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

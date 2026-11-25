import OAI.Hierarchy.ProbeFixedWideTerminalRate
import OAI.Hierarchy.TaggedWireTerminalText
import OAI.Hierarchy.ProtocolRAMTurnRankTextSize
import OAI.Hierarchy.ProbeFixedWideTurnShelfText
import OAI.Hierarchy.ProtocolRAMTurnPaidCost

namespace OAI
/-! # Full instruction classification and fixed text of the true signed terminal -/
set_option quotPrecheck false

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe WireTelescope ProbeStage CoreBoard ReportSockets
open CoreRoute HistoryRoles RoleProgram
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width bits : ℕ)
open CatalystArchive

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem wide_terminal_board_text :
    ∃ cost : ℕ,∀ h width bits work,
      Native.text ((v.wideTerminalBoard h width bits work).extended (v.wideTerminalStock h width bits) (Native.wordBits h (2^v.W) Native.copies))≤cost := by
  obtain ⟨cost,charge⟩:=RoleRoom.fixed_text v.sampler v.W k v.wideJobs v.depth
  refine ⟨cost,?_⟩
  intro h width bits work
  let directory := WideMemory.dir h v.W k v.wideJobs
  let rank := WideMemory.R v.sampler h v.W k
  let hosts := WideMemory.H h v.W k v.wideJobs
  let keys := WideMemory.K h v.W
  let placement := v.widePlacement h width
  let stockBank := v.fixedTerminalStock placement h width
  let slices := v.widePaidSlices h width bits
  let start := v.wideRoleStart h width stockBank slices
  let payment := (v.wideWidthLayout h width slices).bank (events v.mesh).length
  let settlement := TerminalLayout.settlement (v.wideSignedPage h width stockBank) stockBank
  exact charge h rank hosts (v.wideOrder h width) directory
    (BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth
      keys directory.groups hosts rank)
    placement.catalogue start work (CoreCatalogue.headBase h v.W keys directory.groups hosts)
    (CoreCatalogue.pointBits h v.W) (CoreCatalogue.siteBase h v.W keys) (CoreCatalogue.superStart h v.W)
    keys directory.groups hosts payment stockBank settlement.reserved settlement.used (Native.wordBits h (2^v.W) Native.copies)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem wide_terminal_cheap (rom work : ℕ) :
    CheapCode ((v.wideTerminal h width bits rom work).code (Native.wordBits h (2^v.W) Native.copies)
      ((v.wideWidthLayout h width (v.widePaidSlices h width bits)).bank (events v.mesh).length)) := by
  let t := v.wideTerminal h width bits rom work
  let w := Native.wordBits h (2^v.W) Native.copies
  let payment := (v.wideWidthLayout h width (v.widePaidSlices h width bits)).bank (events v.mesh).length
  let totalRows := t.edges+t.routeEntries
  let start := t.rankStart
  change CheapCode (t.code w payment)
  unfold WideCPU.Terminal.code
  exact @cheap_seq w _ _
    (@cheap_seq w _ _ (@Board.extended_cheap t.board t.stock w)
      (@ProtocolRAMTurnPaidCost.rank_cheap w t.edges t.routeEntries
        (ProtocolRAMTurnReplayed.scratch start totalRows) (ProtocolRAMTurnReplayed.rows start totalRows)
        (ProtocolRAMTurnReplayed.groups start totalRows) (ProtocolRAMTurnReplayed.counters start totalRows)
        (ProtocolRAMTurnReplayed.ranks start totalRows t.edges) (ProtocolRAMTurnReplayed.original t.accounts payment)
        (ProtocolRAMTurnReplayed.weight start totalRows) (ProtocolRAMTurnReplayed.key start totalRows)))
    (@ProtocolRAMChronologicalShelf.cheap w t.turns t.sites t.seats t.header t.headerBits t.startColumn t.source
      t.sourceBits t.rom t.romBits t.base t.scratch t.sink t.columns t.heads t.walk)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem wide_terminal_code : ∃ bound : ℕ,∀h width bits rom work,
    Native.text ((v.wideTerminal h width bits rom work).code (Native.wordBits h (2^v.W) Native.copies)
      ((v.wideWidthLayout h width (v.widePaidSlices h width bits)).bank (events v.mesh).length))≤bound := by
  obtain ⟨C,board⟩:=v.wide_terminal_board_text
  refine ⟨C+1137+11098,?_⟩
  intro h width bits rom work
  let t:=v.wideTerminal h width bits rom work
  let bank:=(v.wideWidthLayout h width (v.widePaidSlices h width bits)).bank (events v.mesh).length
  change Native.text (t.code (Native.wordBits h (2^v.W) Native.copies) bank)≤_
  simp only [WideCPU.Terminal.code,Native.text_seq,ProtocolRAMTurnText.rank_text_exact]
  have tail:=v.wide_turn_shelf_text_exact h width bits rom work
  have first:=board h width bits work
  exact Nat.add_le_add (Nat.add_le_add_right first 1137) tail.le

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

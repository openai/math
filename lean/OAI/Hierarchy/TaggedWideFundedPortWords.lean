import OAI.Hierarchy.TaggedWideFundedReceiptCuts
import OAI.Hierarchy.TaggedWideWindowPorts

namespace OAI
/-! # Original native slot words at the funded terminal window -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open scoped Classical BigOperators Fin.CommRing
open Tagged Tagged.WideStack
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ B : ℝ} (x : WideParent κ B)
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
local notation "h" => x.h
local notation "width" => x.w
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))*2^h

open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "rows" => (P).catalogue.rows
local notation "order" => v.wideOrder h width

local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "original" => TerminalLayout.reserve start cnt page
local notation "L" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "C" => v.wideSignedChart h width stock
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width

local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
local notation "o" => wideRouteOrder h D k

variable (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D)
local notation "bits" => v.maxBits
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock v.radius π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock v.radius π o seed
local notation "hi" => v.wideRoleStart h width stock ss
local notation "full" => v.wideFundedSize h width bits

local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "pub" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K (directory).groups H R
local notation "coreTop" => CoreCatalogue.top h v.W K (directory).groups H R
local notation "coreHead" => CoreCatalogue.headBase h v.W K (directory).groups H

local notation "place" => siteNumber h D k
local notation "mount" => (P).catalogue.coreMount π place order chk
local notation "ord" => CoreRoute.enum mount o
local notation "ci" => fun i : Commodity (Fin (2^h)) N k=>PurchaseInventory.slot i

local notation "pair" => pairKeys (Columns h D) k
variable (horizon : full≤ size) (age : v.wideFundedHeight≤ h) (budget : v.keepLimit*width+1≤2^h)
    (small : width≤2^h)
local notation "days" => v.birthMarks P h width r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows) mid
variable {dates : Dates C mid L pay num width} {pos : 0< num}
local notation "issues" => CatalystArchive.issued (chart := C) (initial := mid) («L» := L) (base := pay) (count := num) (payload := width) dates
local notation "who" => CatalystArchive.nativeSite (count := num) (payload := width) («w» := w) L v.mesh issues pos chk
local notation "dur" => CatalystArchive.debit (count := num) (payload := width) v.mesh issues
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))

local notation "closed" => ReserveUse.output original old supply who dur archive
local notation "nativeRows" => (sink).terminalRows closed ord ci (fun j=>(pair j).val)

local notation "settled" => (sink).output closed ord ci (fun j=>(pair j).val)
variable (ell unitCost : ℕ)
  (geometry : Geometry (boardLayout h D k width supply) v.radius 1 nativeRows)
  (actual : v.FundedCutRows h width size π raw nativeRows geometry unitCost)
local notation "g₀" => v.wideDated h width ell unitCost
local notation "port" => FundedCutRows.port v x size π raw unitCost nativeRows geometry actual
local notation "oldRows" => atScale ((P).catalogue.transport order) (fun _=>0) 0 nativeRows
local notation "Live" => ProtocolRAMPackedPlacement.Live oldRows width
variable (operandAge : v.wideOperandHeight≤h) (room : full<2^w)
  (role : Memory w) (low : ∀a,a<full→ role a=settled a)

include horizon age budget small operandAge room low in
/-- The literal native slot operand reads the same supported socket as the funded
row, using the archived physical source in both catalogue summands. -/
theorem FundedCutRows.ordered_slot (i : Live) (side : Bool) :
    ((g₀).orderedSlot side).eval role (i.val.val:Word w)=((port side i.val).val:Word w) := by
  have count : recordCount v.mesh issues=cnt :=
    recordCount_rowOnly v.mesh issues decl (issued_rows dates)
  let : Nonempty (Fin k) := ⟨⟨0, v.positive⟩⟩
  have exclusive : Exclusive days := by apply v.paid_days_exclusive
  have literal := v.wideWindow_literal_ports h width size v.radius π raw horizon age budget small
    operandAge count who dur pair days exclusive actual.sourceAlignment ell unitCost x.formats.2.1
    role low room i side
  have located := congrArg (fun f : (Live × Bool ↪ Fin (directory).groups × Fin H) =>
    ((f (i, side)).2.val : Word w)) (actual.aperture_eq exclusive x.formats.2.1).symm
  have read := FundedCutRows.port_read v x size π raw unitCost nativeRows geometry actual i side
  exact literal.trans (located.trans (congrArg (fun j : Fin H => (j.val : Word w)) read))


variable (m short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
local notation "layout" => v.wideInstalledLayout x m ell short u δ ξ unitCost g₀
local notation "work" => v.wideInstalledSize x m ell unitCost g₀

include horizon age budget small operandAge room low in
/-- At the architectural output of the native local dates the two mounted input
banks contain the scaled port on every supported original row. -/
theorem FundedCutRows.port_words (before : Memory w)
    (slotStage : ∀b (i : Fin rows), ((g₀).slotBank work b).read before (i.val:Word w)=
      ((g₀).lanes:Word w)*((g₀).orderedSlot b).eval role (i.val:Word w)) :
    ∀t side (j:Live),
      (if side then ((layout).inputs t).right else ((layout).inputs t).left).read before (j.val.val:Word w)=
        ((port side j.val).val*2^ell:ℕ) := by
  intro t side j
  have literal := FundedCutRows.ordered_slot v x size π raw horizon age budget small
    ell unitCost geometry actual operandAge room role low j side
  have bank : (if side then ((layout).inputs t).right else ((layout).inputs t).left)=
      (g₀).slotBank work side := by cases side <;> rfl
  rw [bank,slotStage,literal]
  change ((2^ell:ℕ):Word w)*((port side j.val).val:Word w)=((port side j.val).val*2^ell:ℕ)
  rw [Nat.cast_mul,mul_comm]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

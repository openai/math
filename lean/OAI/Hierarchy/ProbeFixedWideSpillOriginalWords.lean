import OAI.Hierarchy.TaggedWireDatedResolved
import OAI.Hierarchy.ProtocolRAMTurnRawWords

namespace OAI
/-! # Archived original site and role words on earlier-live commodity rows -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAMTurnRawWords
open Computability.VPVNP.BurstRAM PrivateRAM
open AdaptiveProbe ProbeStage CoreBoard HistoryRoles RoleProgram ProtocolRAM
open scoped Fin.CommRing Classical

variable {h W k attempts w : ℕ} (S : PurchaseSampler)

/-- The original board writes both unsorted sites and sorted role identifiers for every
authentic source, even when its final stored amount vanishes. -/
theorem original_fields (b : Board) (g : Inventory) (i : Fin b.old)
    (p : Bool→Public S h W k attempts) (initial m : Memory w) (ready : b.Ready w)
    (fit : ∀j,(b.rawFields g j).Fits w b.base) (room : b.endAt+3*b.old<2^w)
    (frame : ∀a < b.endAt+3*b.old,m a=b.extendedState g initial a)
    (seen : ∀side,Resolved S b.chart (b.before side) initial (i.val:Word w) (p side))
    (siteRoom : siteLast h (2^W) k+1≤2^w) (side : Bool) :
    (b.forwardSite side).read m (i.val:Word w)=((name (HistoryRoles.site S (p side))).val:Word w) ∧
    (b.oldSite side).read m (i.val:Word w)=(ProtocolRAMTurnOperands.printed S false p side true:Word w) ∧
    (b.oldRole side).read m (i.val:Word w)=(ProtocolRAMTurnOperands.printed S false p side false:Word w) := by
  obtain ⟨_,cells,earlier⟩:=b.extended_exec g initial ready fit room
  have native:=b.old_observed S initial ready i p seen siteRoom side
  have index:=i.isLt
  have atWord (base : ℕ) (state : Memory w) :
      (RoleROM.bank base b.old).read state (i.val:Word w)=state (base+i.val) := by
    rw [Bank.read,Fin.val_cast_of_lt (show i.val<2^w by omega)]
    change state (base+i.val%ProtocolRAMPurchaseSampler.span b.old)=state (base+i.val)
    rw [Nat.mod_eq_of_lt (i.isLt.trans (ProtocolRAMPurchaseSampler.lt_span _))]
  have low (a : ℕ) (ha : a+b.old≤b.endAt) :
      (RoleROM.bank a b.old).read m (i.val:Word w)=(RoleROM.bank a b.old).read (b.final initial) (i.val:Word w) := by
    rw [atWord,atWord]
    exact (frame _ (by omega)).trans (earlier _ (by omega))
  constructor
  · have line (j : Fin 3) :
        (RoleROM.bank (b.endAt+j.val*b.old) b.old).read m (i.val:Word w)=(b.rawFields g j).eval initial (i.val:Word w) := by
      rw [atWord]
      exact (frame _ (by fin_cases j <;> simp <;> omega)).trans (cells j i)
    cases side
    · exact (line 0).trans (seen false).1
    · exact (line 1).trans (seen true).1
  · constructor
    · exact (low _ (by unfold Board.endAt Board.newBase;cases side <;> simp <;>omega)).trans
        (native.1.trans (ProtocolRAMTurnOperands.actual_word S false p side true))
    · exact (low _ (by unfold Board.endAt Board.newBase;cases side <;> simp <;>omega)).trans
        (native.2.trans (ProtocolRAMTurnOperands.actual_word S false p side false))


end Hierarchy.ProtocolRAMTurnRawWords
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
set_option maxRecDepth 8192
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
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
local notation "sheet" => v.wideSignedPage h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "original" => TerminalLayout.reserve start cnt page
local notation "L" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "C" => v.wideSignedChart h width stock
local notation "last" => (events v.mesh).length
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width


local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
local notation "market" => v.catalystMarkets P h width
local notation "o" => wideRouteOrder h D k


variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (bits : ℕ)
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock M π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o seed
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
local notation "lw" => v.wideWidthLayout h width ss
local notation "last" => (events v.mesh).length

variable (horizon : v.wideFundedSize h width bits ≤ size) (age : v.wideFundedHeight≤h)
  (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) (operandAge : v.wideOperandHeight≤h)
  (issues : Attempt→CatalystArchive.Entry (Fintype.card (Columns h (2^v.W))*k) width)
  (card : recordCount v.mesh issues = rowOnlyCount v.mesh (declaredRows v.mesh
    (ownerLedger (v.nativeBoards (v.widePlacement h width) h width) v.mesh
      (v.widePlacement h width).catalogue (v.widePlacement h width).routes F
      (v.privateArena (v.widePlacement h width) h width))))
  (who : Fin (recordCount v.mesh issues)→Fin (Fintype.card (Columns h (2^v.W))*k))
  (cj : Columns h (2^v.W)×Fin k→Fin (Fintype.card (Columns h (2^v.W))*k))
local notation "dur" => CatalystArchive.debit v.mesh issues
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))
local notation "closed" => ReserveUse.output original old supply who dur archive
local notation "settled" => (sink).output closed ord ci (fun j=>(cj j).val)
local notation "rawRow" => (sink).terminalRows closed ord ci (fun j=>(cj j).val)
local notation "counts" => fun e : Fin rows=>(rawRow e).width
variable (marks : Marks h v.W k v.wideJobs) (unique : Exclusive marks)
    (A₀ : WideFundedTurnAlignment v h width size M π raw bits issues who cj marks)

local notation "paid" => PaidWidths.total ss chk
local notation "goods" => fun i : Commodity (Fin (2^h)) N k=>RouteSettlement.actual (old).stock closed (ci i)
local notation "held" => fun j : Columns h D×Fin k=>RouteSettlement.actual (old).reserved closed (cj j).val
local notation "taken" => fun j : Columns h D×Fin k=>RouteSettlement.actual (old).used closed (cj j).val
local notation "term" => (mount).actual.chordWidths paid+(commodityGraph π place).chordWidths goods+
  (catalystGraph place).chordWidths (fun j=>held j-taken j)

local notation "shape" => RoleRoom.shape («R»:=WideMemory.R v.sampler h v.W k) v.sampler directory rows
local notation "z" => shape
local notation "ports" => livePort v.sampler (P).catalogue π marks unique order (v.wideBoughtOrdinal h width π marks) A₀
local notation "oldRows" => Fintype.card (Old h v.W k rows)
local notation "value" => v.wideDatedValue h width bits mid chk issues
local notation "tb" => v.wideTerminalBoard h width bits 0

include horizon age budget small operandAge card

/-- Original sorted and directed role words of a real commodity or reserve at every
date, including dates at which its eventual terminal value is zero. -/
theorem wide_spill_original_goods (start₀ : ℕ) (initial m : Memory w)
    (keep : ∀x,x<full→initial x=settled x)
    (highFit : (z).ceiling hi<2^w) (oldRoom : oldRows≤2^w)
    (i : Fin oldRows) (g₀ : Goods h v.W k ⊕ Catalysts h v.W k)
    (goodsKey : SettledMatrix.Layout.numbered (I:=Goods h v.W k) («A»:=Catalysts h v.W k) («r»:=rows) i=.inr g₀)
    (ok : (v.wideTerminalBoard h width bits start₀).Ready w)
    (fits : ∀j,((v.wideTerminalBoard h width bits start₀).rawFields (v.wideTerminalStock h width bits) j).Fits w start₀)
    (room : (v.wideTerminalBoard h width bits start₀).endAt+3*oldRows<2^w)
    (frame : ∀a<(v.wideTerminalBoard h width bits start₀).endAt+3*oldRows,
      m a=(v.wideTerminalBoard h width bits start₀).extendedState (v.wideTerminalStock h width bits) initial a)
    (sites : siteLast h D k+1≤2^w) (side : Bool) :
    let b:=v.wideTerminalBoard h width bits start₀
    let port:=publicRoleFor v.sampler π (activePaid v.sampler counts ports) (.inr g₀)
    (b.forwardSite side).read m (i.val:Word w)=((name (HistoryRoles.site v.sampler (port side))).val:Word w) ∧
    (b.oldSite side).read m (i.val:Word w)=(ProtocolRAMTurnOperands.printed v.sampler false port side true:Word w) ∧
    (b.oldRole side).read m (i.val:Word w)=(ProtocolRAMTurnOperands.printed v.sampler false port side false:Word w) := by
  intro b port
  refine ProtocolRAMTurnRawWords.original_fields v.sampler b (v.wideTerminalStock h width bits) i port initial m ok fits room frame ?_ sites side
  intro pol
  have actual := v.wide_original_resolved h width size M π raw bits horizon age budget small operandAge
    issues card who cj marks unique A₀ initial keep highFit oldRoom i (by rw [goodsKey]; trivial) pol
  change Resolved v.sampler ((z).chart hi) ((tb).before pol) initial (i.val : Word w)
    (publicRoleFor v.sampler π (activePaid v.sampler counts ports) (.inr g₀) pol)
  rw [← goodsKey]
  exact actual

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

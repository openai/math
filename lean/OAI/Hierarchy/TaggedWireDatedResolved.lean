import OAI.Hierarchy.TaggedWireFundedReport
import OAI.Hierarchy.ProbeFixedWideDatedAmounts
import OAI.Hierarchy.ProbeFixedWideTerminal

namespace OAI
/-! # The original positive site role for each dated prefix -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
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

/-- Every inventory and reserve socket has a fixed public role. Only paid slots require a positive original width. -/
theorem wide_original_resolved (m : Memory w)
    (keep : ∀x,x<full→m x=settled x)
    (highFit : (z).ceiling hi<2^w) (oldRoom : oldRows≤2^w)
    (i : Fin oldRows) (on : match SettledMatrix.Layout.numbered (I:=Goods h v.W k) («A»:=Catalysts h v.W k) («r»:=rows) i with
      | .inl e=>0<counts e | .inr _=>True) (side : Bool) :
    Resolved v.sampler ((z).chart hi) ((tb).before side) m (i.val:Word w)
      (publicRoleFor v.sampler π (activePaid v.sampler counts ports) (SettledMatrix.Layout.numbered i) side) := by
  have inputs:=v.wide_funded_turn_inputs h width size M π raw bits horizon age budget small (entries:=recordCount v.mesh issues) card who dur
    (I:=Commodity (Fin (2^h)) N k) (J:=Columns h D × Fin k)
    (core:=(mount).ordinary) (center:=(mount).centers) ord ci (fun t=>(cj t).val) m keep
  have core:=inputs.2.2.2.1
  have capacity:=v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width)
    ((le_max_left ..).trans age) budget
  have sizes:=v.wide_operand_room h width operandAge capacity.2
  have bounds : (z).publicRows≤(z).ceiling hi ∧ (z).signedSites≤(z).ceiling hi := by
    simp only [RoleRoom.Sizes.ceiling,RoleRoom.Sizes.stop,RoleRoom.Sizes.offset,RoleRoom.Sizes.positive,
      RoleRoom.Sizes.axis,RoleRoom.Sizes.ext,RoleRoom.Sizes.free,RoleRoom.Sizes.pub]
    omega
  have ax : (siteLast h D k+1)*(2*k)≤2^w:=bounds.2.trans highFit.le
  have factor : 1≤2*k:=by have hk:=v.positive; omega
  have sites : siteLast h D k+1≤2^w :=
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (siteLast h D k+1) factor : _≤_).trans ax
  have wide : 4≤2^w:=by
    have low : 4≤(z).ceiling hi := by
      have nonzero : 0<(z).signedSites := Nat.mul_pos (Nat.succ_pos _) (by omega : 0<2*k)
      unfold RoleRoom.Sizes.ceiling RoleRoom.Sizes.stop RoleRoom.Sizes.offset RoleRoom.Sizes.positive
        RoleRoom.Sizes.axis RoleRoom.Sizes.ext RoleRoom.Sizes.free RoleRoom.Sizes.pub
      omega
    exact low.trans highFit.le
  have perm (j : Fin (2^h)) : m j.val=((π j).val:Word w):=by
    have atKey:=core.board.input j
    change m (0+(j.val:Word w).val%2^h)=_ at atKey
    rw [Fin.val_cast_of_lt (j.isLt.trans (v.date_prefix_fit h)),Nat.mod_eq_of_lt j.isLt,Nat.zero_add] at atKey
    exact atKey
  have paidRoom : rows<2^w:=by
    have expression:=v.wide_old_rows h width
    have goodsPos : 0<PurchaseInventory.footprint h N k:=by
      unfold PurchaseInventory.footprint
      positivity
    omega
  have sockets:=v.wide_resolved_paid h width hi M π marks unique A₀ m
    inputs.2.2.2.2.1 core inputs.1 inputs.2.1 (fun e=>inputs.2.2.2.2.2.1 e.1 _)
    sizes.1 highFit paidRoom sizes.2.1 sizes.2.2.1 sizes.2.2.2
  apply RoleRoom.mixed_original v.sampler order directory π hi m inputs.1 oldRoom (P).catalogue.core
    core.board.rows wide sites (bounds.1.trans highFit.le) (v.date_prefix_fit h).le ax perm
    (v.widePaidPorts h width hi) counts counts (fun _=>1) (fun _=>1) (fun _=>0) (fun _=>le_rfl) ports sockets i _ side
  change 0<SettledMatrix.Layout.available _ _ _ _ (SettledMatrix.Layout.numbered i)
  cases key : SettledMatrix.Layout.numbered (I:=Goods h v.W k) («A»:=Catalysts h v.W k) («r»:=rows) i with
  | inl e =>
    simpa only [key,SettledMatrix.Layout.available,Sum.elim_inl] using on
  | inr x => cases x <;> exact Nat.zero_lt_one

/-- Original paid, commodity and catalyst sockets at any earlier date of the
same chart. A positive earlier paid slice belongs to the original report by
additivity, including rows whose residual budget subsequently vanishes. -/
theorem wide_dated_old_resolved (m : Memory w)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (keep : ∀x,x<full→m x=settled x)
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (highFit : (z).ceiling hi<2^w) (oldRoom : oldRows≤2^w)
    (j : ℕ) (i : Fin oldRows) (on : 0<value j (SettledMatrix.Layout.numbered i)) (side : Bool) :
    Resolved v.sampler ((z).chart hi) ((tb).before side) m (i.val:Word w)
      (publicRoleFor v.sampler π (activePaid v.sampler counts ports) (SettledMatrix.Layout.numbered i) side) := by
  have capacity:=v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width)
    ((le_max_left ..).trans age) budget
  have support (e : Fin rows) : PaidWidths.total (PrefixWidths.prefixRows (events v.mesh)
      (v.wideEventSlices h width bits) j) chk e≤counts e := by
    have prior:=PrefixWidths.prefix_total_le (events v.mesh) (v.wideEventSlices h width bits) chk j e
    rw [v.wideEventSlices_flat] at prior
    exact prior.trans ((v.wide_terminal_width_at h width size M π seed who dur cj ss
      (v.wide_funded_stock_at_size h width M π raw bits size horizon age budget small)
      (v.wide_funded_paid_at_size h width M π raw bits size horizon age budget small)
      capacity.1 cost baseline e).2)
  apply v.wide_original_resolved h width size M π raw bits horizon age budget small operandAge
    issues card who cj marks unique A₀ m keep highFit oldRoom i _ side
  cases key : SettledMatrix.Layout.numbered (I:=Goods h v.W k) («A»:=Catalysts h v.W k) («r»:=rows) i with
  | inl e =>
    exact lt_of_lt_of_le (by simpa only [key,wideDatedValue,Sum.elim_inl] using on) (support e)
  | inr x => trivial

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

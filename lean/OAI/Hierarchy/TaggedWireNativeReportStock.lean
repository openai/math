import OAI.Hierarchy.TaggedWireFixedTerminalStock
import OAI.Hierarchy.TaggedWireNativeReport
import OAI.Hierarchy.ProbeFixedWireUsedAt

namespace OAI
/-! # Chronological terminal goods and reserve of the native selected report -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option cleanup.letToHave false
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
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width


local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
local notation "market" => v.catalystMarkets P h width
local notation "o" => wideRouteOrder h D k


variable (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (bits : ℕ)
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
local notation "lw" => v.wideWidthLayout h width ss
local notation "last" => (events v.mesh).length

local notation "pair" => pairKeys (Columns h D) k
private abbrev reportCost :=
  ∀e : Fin rows, PaidWidths.total ss chk e + (v.overflowFactor v.keepLimit + fuel v.mesh) * width < 2^w

variable (horizon : v.wideFundedSize h width bits ≤ size) (age : v.wideFundedHeight ≤ h)
    (budget : v.keepLimit * width + 1 ≤ 2^h) (small : width ≤ 2^h)
    (cost : reportCost v h width size π raw bits)
local notation "days" => v.birthMarks P h width r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows) mid
private abbrev reportDates := Dates C mid L pay num width

variable {dates : reportDates v h width size π raw bits} {pos : 0 < Fintype.card (Columns h (2^v.W)) * k}
private def reportEntries (entries : reportDates v h width size π raw bits) : Attempt → Entry num width :=
  CatalystArchive.issued (chart := C) (initial := mid) («L» := L) (base := pay)
    (count := num) (payload := width) entries
local notation "issues" => reportEntries v h width size π raw bits dates

private def reportSites (entries : reportDates v h width size π raw bits) (positive : 0 < num) :
    Fin (recordCount (count := num) (payload := width) v.mesh (reportEntries v h width size π raw bits entries)) → Fin num :=
  CatalystArchive.nativeSite (count := num) (payload := width) («w» := w) L v.mesh
    (reportEntries v h width size π raw bits entries) positive chk
local notation "who" => reportSites v h width size π raw bits dates pos
local notation "dur" => CatalystArchive.debit (count := num) (payload := width) v.mesh issues
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))

attribute [local irreducible] ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec
  CatalystArchive.recordCount CatalystArchive.issued
  CatalystArchive.nativeSite CatalystArchive.debit

private theorem report_stock_for_dates (cert : Whole.Reconciliation (I:=Commodity (Fin (2^h)) N k) (J:=Columns h D × Fin k) (n:=recordCount (count:=num) (payload:=width) v.mesh issues) (count:=num) («w»:=w) sink original supply who dur ord ci pair archive)
    (names : v.WideFundedAlignment h width size bits π raw who dur (fun j=>(pair j).val))
    (i : Commodity (Fin (2^h)) N k) :
    let Z:=v.wide_report_for_dates h width size π raw bits horizon age budget small cost (dates:=dates) (pos:=pos) cert names
    Z.stock i=(chk ((stock).base+PurchaseInventory.slot i)).val ∧
      Z.stock i=v.wireGoodsAt h width last (run C (events v.mesh) mid) i :=
  v.wide_report_stock_at (h:=h) (width:=width) (size:=size) (M:=v.radius) (π:=π) (raw:=raw)
    (bits:=bits) (horizon:=horizon) (age:=age) (budget:=budget) (small:=small) («issues»:=issues)
    («who»:=who) (cj:=pair) (marks:=days) (A₀:=names.1.some) cert names.2 cost i

private abbrev reserveForDatesConclusion (cert : Whole.Reconciliation (I:=Commodity (Fin (2^h)) N k) (J:=Columns h D × Fin k) (n:=recordCount (count:=num) (payload:=width) v.mesh issues) (count:=num) («w»:=w) sink original supply who dur ord ci pair archive)
    (names : v.WideFundedAlignment h width size bits π raw who dur (fun j=>(pair j).val))
    (i : Columns h D×Fin k) : Prop :=
    let Z:=v.wide_report_for_dates h width size π raw bits horizon age budget small cost (dates:=dates) (pos:=pos) cert names
    Z.reserved i=supply ∧ Z.used i=Whole.Reconciliation.usedAt (I:=Commodity (Fin (2^h)) N k) (J:=Columns h D × Fin k) cert i

private theorem report_reserve_for_dates (cert : Whole.Reconciliation (I:=Commodity (Fin (2^h)) N k) (J:=Columns h D × Fin k) (n:=recordCount (count:=num) (payload:=width) v.mesh issues) (count:=num) («w»:=w) sink original supply who dur ord ci pair archive)
    (names : v.WideFundedAlignment h width size bits π raw who dur (fun j=>(pair j).val))
    (i : Columns h D×Fin k) :
    reserveForDatesConclusion v h width size π raw bits horizon age budget small cost (dates:=dates) (pos:=pos) cert names i := by
  unfold reserveForDatesConclusion
  intro Z
  constructor
  · let measured := ReserveUse.reported original old supply who dur archive cert.archive (pair i) cert.usedSize
      cert.reserveSize (cert.funded _) cert.word
    exact measured.2
  · rfl

attribute [local irreducible] wide_report_for_dates

-- Reuse the dates, reconciliation, and alignment supplied to the selected report.
open Lean Elab Term in
local elab "observeReport " observer:ident selected:ident idx:ident : term => do
  let fn ← resolveGlobalConstNoOverload observer
  let helper ← Meta.mkConstWithFreshMVarLevels fn
  let i ← Meta.getFVarFromUserName idx.getId
  let actual ← Meta.getLocalDeclFromUserName selected.getId
  let some value := actual.value? | throwError "expected the selected native report"
  let result ← Meta.whnf value
  unless result.getAppFn.isConstOf ``wide_report_for_dates do
    throwError "expected native report construction, got {result.getAppFn.constName?}"
  return mkAppN helper (result.getAppArgs.push i)


private abbrev stockConclusion (state : Word w) (names : ∀{n : ℕ}(owner : Fin n→Fin num)(fees : Fin n→ℕ),
    v.WideFundedAlignment h width size bits π raw owner fees (fun j=>(pair j).val))
    (i : Commodity (Fin (2^h)) N k) : Prop :=
    let Z:=v.wide_native_report h width size π raw bits horizon age budget small cost state names
    Z.stock i=(chk ((stock).base+PurchaseInventory.slot i)).val ∧
      Z.stock i=v.wireGoodsAt h width last (run C (events v.mesh) mid) i

/-- The report chosen by the authentic run, on this particular original input
and initial machine state, contains exactly the final temporal goods vector. -/
theorem wide_native_report_stock (state : Word w) (names : ∀{n : ℕ}(owner : Fin n→Fin num)(fees : Fin n→ℕ),
    v.WideFundedAlignment h width size bits π raw owner fees (fun j=>(pair j).val))
    (i : Commodity (Fin (2^h)) N k) :
    stockConclusion v h width size π raw bits horizon age budget small cost state names i := by
  let selected := v.wide_native_report h width size π raw bits horizon age budget small cost state names
  exact observeReport report_stock_for_dates selected i



private theorem connectReserved (reserved capacity used paid checkout state terminal : ℕ)
    (report : reserved = capacity ∧ used = paid) (totals : checkout = paid ∧ state = paid)
    (atEnd : state = terminal) :
    reserved = capacity ∧ used = checkout ∧ used = terminal :=
  ⟨report.1,report.2.trans totals.1.symm,(report.2.trans totals.2.symm).trans atEnd⟩

-- Apply transitivity using the exact natural-number terms in the three observations.
open Lean Elab Tactic in
local elab "finishReport " observations:ident totals:ident atEnd:ident : tactic => withMainContext do
  let report ← Meta.getFVarFromUserName observations.getId
  let amount ← Meta.getFVarFromUserName totals.getId
  let lastValue ← Meta.getFVarFromUserName atEnd.getId
  let equality (value : Lean.Expr) := do
    let eq ← Meta.whnf value
    unless eq.getAppFn.isConstOf ``Eq do throwError "expected a reserve equality"
    return (eq.getAppArgs[1]!, eq.getAppArgs[2]!)
  let conjuncts (proof : Lean.Expr) := do
    let type ← Meta.whnf (← Meta.inferType proof)
    unless type.getAppFn.isConstOf ``And do throwError "expected the two reserve observations"
    return (← equality type.getAppArgs[0]!, ← equality type.getAppArgs[1]!)
  let ((reserved0,supply0),(used0,paid0)) ← conjuncts report
  let ((checkout0,_),(state0,_)) ← conjuncts amount
  let (_,terminal0) ← equality (← Meta.inferType lastValue)
  let proof := mkAppN (mkConst ``connectReserved)
    #[reserved0,supply0,used0,paid0,checkout0,state0,terminal0,report,amount,lastValue]
  (← getMainGoal).assign proof
  replaceMainGoal []

private abbrev reserveConclusion (state : Word w) (names : ∀{n : ℕ}(owner : Fin n→Fin num)(fees : Fin n→ℕ),
    v.WideFundedAlignment h width size bits π raw owner fees (fun j=>(pair j).val))
    (i : Columns h D×Fin k) : Prop :=
    let Z:=v.wide_native_report h width size π raw bits horizon age budget small cost state names
    Z.reserved i=supply ∧ Z.used i=v.wireUsedAt h width last chk i ∧
      Z.used i=v.wireUsedAt h width last (run C (events v.mesh) mid) i

/-- The same selected run's reserved and used fields are the original supply
and the actual cumulative debit through the end of the calendar. -/
theorem wide_native_report_reserve (state : Word w) (names : ∀{n : ℕ}(owner : Fin n→Fin num)(fees : Fin n→ℕ),
    v.WideFundedAlignment h width size bits π raw owner fees (fun j=>(pair j).val))
    (i : Columns h D×Fin k) :
    reserveConclusion v h width size π raw bits horizon age budget small cost state names i := by
  let selected := v.wide_native_report h width size π raw bits horizon age budget small cost state names
  have observations := observeReport report_reserve_for_dates selected i
  have totals := (v.wide_wire_reserve h width size bits horizon age budget small π raw state i).2
  have terminal : StockBound.state C mid last = run C (events v.mesh) mid := by
    change run C ((events v.mesh).take (events v.mesh).length) mid = _
    rw [List.take_length]
  have lastValue := congrArg (fun z => v.wireUsedAt h width last z i) terminal
  finishReport observations totals lastValue



end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

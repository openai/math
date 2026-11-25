import OAI.Hierarchy.TaggedWireNativeReportStock
import OAI.Hierarchy.TaggedWireFundedExecution
import OAI.Hierarchy.ProbeFixedWirePaidChronology

namespace OAI
/-! # The exact row ordering and widths at the terminal state of a signed path -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open scoped Classical Fin.CommRing
set_option maxRecDepth 8192
set_option maxHeartbeats 3200000
set_option cleanup.letToHave false
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

local notation "pair" => pairKeys (Columns h D) k
private abbrev terminalVectorCost :=
  ∀e : Fin rows, PaidWidths.total ss chk e + (v.overflowFactor v.keepLimit + fuel v.mesh) * width < 2^w

variable (horizon : v.wideFundedSize h width bits ≤ size) (age : v.wideFundedHeight ≤ h)
    (budget : v.keepLimit * width + 1 ≤ 2^h) (small : width ≤ 2^h)
    (cost : terminalVectorCost v h width size π raw bits)
open LinearAlgebra.SpectralBooks ChordGraph
local notation "es" => events v.mesh
local notation "endRam" => run C es mid
local notation "stored" => (P).catalogue.coreMount π (siteNumber h D k) (v.wideOrder h width) chk
local notation "live" => (P).catalogue.coreMount π (siteNumber h D k) (v.wideOrder h width) endRam
local notation "charges" => v.wirePaidAt h width bits last endRam
private abbrev terminalVectorNames := ∀{n : ℕ}(owner : Fin n→Fin num)(fees : Fin n→ℕ),
    v.WideFundedAlignment h width size bits π raw owner fees (fun j=>(pair j).val)
variable (state : Word (Native.wordBits h (2^v.W) Native.copies)) (names : terminalVectorNames v h width size π raw bits)
local notation "Z" => v.wide_native_report h width size π raw bits horizon age budget small cost state names

private theorem equal_live_widths {sites n : ℕ} (leftGraph rightGraph : PortGraph (Fin sites) (Fin n)) (b : Fin n→ℕ)
    (hh : ∀i,0<b i→leftGraph.tail i=rightGraph.tail i ∧ leftGraph.head i=rightGraph.head i) :
    leftGraph.chordWidths b=rightGraph.chordWidths b := by
  classical
  unfold PortGraph.chordWidths
  apply Finset.sum_congr rfl
  intro e _
  by_cases on : 0<b e
  · rw [chordWidth_scaled leftGraph e (b e),chordWidth_scaled rightGraph e (b e),(hh e on).1,(hh e on).2]
  · have zero : b e=0:=by omega
    simp [chordWidth_scaled,zero]

private theorem fullEventRows (dates : List Event) (compile : Event → List PaidWidths.Slice) :
    PrefixWidths.prefixRows dates compile dates.length = dates.flatMap compile := by
  simp only [PrefixWidths.prefixRows, List.take_length]

private theorem addWidthsEq {sites : ℕ} {a b c d e f : Widths sites}
    (hd : a = d) (he : b = e) (hf : c = f) : a+b+c=d+e+f :=
  congrArg₂ (· + ·) (congrArg₂ (· + ·) hd he) hf

private theorem terminalWireSum (m : Memory w) :
    v.wireAt h width bits π last m =
      ((P).catalogue.coreMount π (siteNumber h D k) (v.wideOrder h width) m).actual.chordWidths (v.wirePaidAt h width bits last m) +
      (commodityGraph π (siteNumber h D k)).chordWidths (v.wireGoodsAt h width last m) +
      (catalystGraph (siteNumber h D k)).chordWidths (fun i => fuel v.mesh*width-v.wireUsedAt h width last m i) := rfl

attribute [local irreducible] PortGraph.chordWidths commodityGraph catalystGraph siteNumber

private abbrev terminalLedgerConclusion : Prop :=
    (Z).mount.actual.chordWidths (Z).fixed+(commodityGraph π (siteNumber h D k)).chordWidths (Z).stock+
      (catalystGraph (siteNumber h D k)).chordWidths (fun i=>(Z).reserved i-(Z).used i)=
        v.wireAt h width bits π last endRam

private abbrev vectorReportDates := Dates C mid L pay num width

variable {dates : vectorReportDates v h width size π raw bits} {pos : 0 < Fintype.card (Columns h (2^v.W)) * k}
private def vectorReportEntries (entries : vectorReportDates v h width size π raw bits) : Attempt → Entry num width :=
  CatalystArchive.issued (chart := C) (initial := mid) («L» := L) (base := pay)
    (count := num) (payload := width) entries
local notation "issues" => vectorReportEntries v h width size π raw bits dates

private def vectorReportSites (entries : vectorReportDates v h width size π raw bits) (positive : 0 < num) :
    Fin (recordCount (count := num) (payload := width) v.mesh (vectorReportEntries v h width size π raw bits entries)) → Fin num :=
  CatalystArchive.nativeSite (count := num) (payload := width) («w» := w) L v.mesh
    (vectorReportEntries v h width size π raw bits entries) positive chk
local notation "who" => vectorReportSites v h width size π raw bits dates pos
local notation "dur" => CatalystArchive.debit (count := num) (payload := width) v.mesh issues
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))

attribute [local irreducible] ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec
  CatalystArchive.recordCount CatalystArchive.issued
  CatalystArchive.nativeSite CatalystArchive.debit

private abbrev datedCoreWidth (cert : Whole.Reconciliation (I:=Commodity (Fin (2^h)) N k) (J:=Columns h D × Fin k) (n:=recordCount (count:=num) (payload:=width) v.mesh issues) (count:=num) («w»:=w) sink original supply who dur ord ci pair archive)
    (names : v.WideFundedAlignment h width size bits π raw who dur (fun j=>(pair j).val))
    : Prop :=
  let report := v.wide_report_for_dates h width size π raw bits horizon age budget small cost (dates:=dates) (pos:=pos) cert names
  report.mount.actual.chordWidths report.fixed =
    (stored).actual.chordWidths (PaidWidths.total (edges:=rows) ss chk)

private theorem nativeDatedCoreWidth (cert : Whole.Reconciliation (I:=Commodity (Fin (2^h)) N k) (J:=Columns h D × Fin k) (n:=recordCount (count:=num) (payload:=width) v.mesh issues) (count:=num) («w»:=w) sink original supply who dur ord ci pair archive)
    (names : v.WideFundedAlignment h width size bits π raw who dur (fun j=>(pair j).val))
    : datedCoreWidth v h width size π raw bits horizon age budget small cost (dates:=dates) (pos:=pos) cert names := by
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let equality ← Lean.Meta.whnf (← goal.getType)
      goal.assign (← Lean.Meta.mkEqRefl equality.getAppArgs.back!)

attribute [local irreducible] wide_report_for_dates

-- Reuse the dated reconciliation selected by the native run.
open Lean Elab Tactic in
local elab "selectCoreWidth " report:ident : tactic => withMainContext do
  let selected ← Meta.getLocalDeclFromUserName report.getId
  let some value := selected.value? | throwError "expected a selected native report"
  let concrete ← Meta.whnf value
  unless concrete.getAppFn.isConstOf ``wide_report_for_dates do
    throwError "expected a funded report with selected dates"
  let observed ← Meta.mkConstWithFreshMVarLevels ``nativeDatedCoreWidth
  (← getMainGoal).assign (mkAppN observed concrete.getAppArgs)
  replaceMainGoal []

private abbrev assignedCoreWidth : Prop :=
  (Z).mount.actual.chordWidths (Z).fixed =
    (stored).actual.chordWidths (PaidWidths.total (edges:=rows) ss chk)

private theorem nativeCoreWidth : assignedCoreWidth v h width size π raw bits horizon age budget small cost state names := by
  let selected := (Z)
  selectCoreWidth selected

private theorem paidAtCheckout :
    PaidWidths.total (edges:=rows) ss chk = v.wirePaidAt h width bits last chk := by
  have slices := (fullEventRows es (v.wideEventSlices h width bits)).trans (v.wideEventSlices_flat h width bits)
  exact congrArg (fun entries => PaidWidths.total (edges:=rows) entries chk) slices.symm

attribute [local irreducible] wide_native_report wide_report_at wireAt wideFundedSize wideSignedMidAt wideSignedCheckoutAt

private theorem reportGoodsWidth {ι : Type} (reported previous current : ι → ℕ)
    (observation : ∀ i, reported i = previous i ∧ reported i = current i) : reported = current :=
  funext (fun i => (observation i).2)

private theorem reportHeldWidth {ι : Type} (reserved used previous current : ι → ℕ) (capacity : ℕ)
    (observation : ∀ i, reserved i = capacity ∧ used i = previous i ∧ used i = current i) :
    (fun i => reserved i - used i) = (fun i => capacity - current i) :=
  funext (fun i => congrArg₂ Nat.sub (observation i).1 (observation i).2.2)

-- Take the component functions directly from the observed pointwise equalities.
open Lean Elab Tactic in
local elab "collectReport " observation:ident " with " helper:ident : tactic => withMainContext do
  let observed ← Meta.getFVarFromUserName observation.getId
  let aggregate ← Meta.mkConstWithFreshMVarLevels (← resolveGlobalConstNoOverload helper)
  let conjunction (t : Lean.Expr) := do
    let t ← Meta.whnf t
    unless t.getAppFn.isConstOf ``And do throwError "expected a pair of report observations"
    return (t.getAppArgs[0]!, t.getAppArgs[1]!)
  let equality (t : Lean.Expr) := do
    let t ← Meta.whnf t
    unless t.getAppFn.isConstOf ``Eq do throwError "expected an observed value"
    return (t.getAppArgs[1]!, t.getAppArgs[2]!)
  Meta.forallBoundedTelescope (← Meta.inferType observed) (some 1) fun xs body => do
    let domain ← Meta.inferType xs[0]!
    let (first, second) ← conjunction body
    let (a, b) ← equality first
    let second ← Meta.whnf second
    let wrap := fun val => Meta.mkLambdaFVars xs val
    let args ← if second.getAppFn.isConstOf ``Eq then do
      let (_, c) ← equality second
      pure #[domain, ← wrap a, ← wrap b, ← wrap c, observed]
    else do
      let (middle, lastRead) ← conjunction second
      let (used, oldValue) ← equality middle
      let (_, terminal) ← equality lastRead
      pure #[domain, ← wrap a, ← wrap used, ← wrap oldValue, ← wrap terminal, b, observed]
    (← getMainGoal).assign (mkAppN aggregate args)
  replaceMainGoal []

private abbrev terminalGoodsWidth : Prop := (Z).stock = v.wireGoodsAt h width last endRam

private theorem nativeGoodsEq : terminalGoodsWidth v h width size π raw bits horizon age budget small cost state names := by
  let observation := v.wide_native_report_stock h width size π raw bits horizon age budget small cost state names
  collectReport observation with reportGoodsWidth

private abbrev terminalHeldWidth : Prop :=
  (fun i => (Z).reserved i - (Z).used i) = (fun i => fuel v.mesh*width-v.wireUsedAt h width last endRam i)

private theorem nativeHeldEq : terminalHeldWidth v h width size π raw bits horizon age budget small cost state names := by
  let observation := v.wide_native_report_reserve h width size π raw bits horizon age budget small cost state names
  collectReport observation with reportHeldWidth

theorem native_terminal_ledger
    (stable : ∀e,(charges) e=v.wirePaidAt h width bits last chk e)
    (ends : ∀e,0<(charges) e→(live).actual.tail e=(stored).actual.tail e ∧
      (live).actual.head e=(stored).actual.head e) :
    terminalLedgerConclusion v h width size π raw bits horizon age budget small cost state names := by
  have fixed := (paidAtCheckout v h width size π raw bits).trans (funext stable).symm
  have goods := nativeGoodsEq v h width size π raw bits horizon age budget small cost state names
  have heldEq := nativeHeldEq v h width size π raw bits horizon age budget small cost state names
  have graphEq := equal_live_widths (live).actual (stored).actual charges ends
  have measured := nativeCoreWidth v h width size π raw bits horizon age budget small cost state names
  have coreEq := measured.trans ((congrArg (stored).actual.chordWidths fixed).trans graphEq.symm)
  have goodsEq := congrArg (commodityGraph π (siteNumber h D k)).chordWidths goods
  have reserveEq := congrArg (catalystGraph (siteNumber h D k)).chordWidths heldEq
  have totalEq := addWidthsEq coreEq goodsEq reserveEq
  exact totalEq.trans (terminalWireSum v h width π bits endRam).symm

-- Name the input width vector once for the report's dependent row indices.
include width size π raw bits horizon age budget small cost state names in
private def terminalInputWidth : Widths (siteLast h D k + 1) := by
  let selected := (Z)
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let entry ← Lean.Meta.getFVarFromUserName `selected
      let reportType ← Lean.Meta.whnf (← Lean.Meta.inferType entry)
      unless reportType.getAppFn.isConstOf ``CoreBoard.Report do
        throwError "expected a native report"
      goal.assign reportType.getAppArgs.back!

private def terminalInputReport :
    CoreBoard.Report π.symm D k width (fuel v.mesh*width) v.radius 1
      (terminalInputWidth v h width size π raw bits horizon age budget small cost state names) := (Z)

local notation "sourceReport" => terminalInputReport v h width size π raw bits horizon age budget small cost state names

private def retainedRows
    {height depth indexWidth inputWidth allowance radius denominator : ℕ}
    {permutation : Equiv.Perm (Tagged.Row height)} {initial : Widths (siteLast height depth indexWidth+1)}
    (entry : CoreBoard.Report permutation depth indexWidth inputWidth allowance radius denominator initial) :
    (n : ℕ) × (Fin n → ProtocolRAMEmit.Row) :=
  ⟨entry.edges, entry.rows⟩

private def retainedGeometry
    {height depth indexWidth inputWidth allowance radius denominator : ℕ}
    {permutation : Equiv.Perm (Tagged.Row height)} {initial : Widths (siteLast height depth indexWidth+1)}
    (entry : CoreBoard.Report permutation depth indexWidth inputWidth allowance radius denominator initial) :
    (n : ℕ) × (records : Fin n → ProtocolRAMEmit.Row) ×
      ProtocolRAMEmit.Geometry (CoreBoard.boardLayout height depth indexWidth inputWidth allowance) radius denominator records :=
  ⟨entry.edges, entry.rows, entry.geometry⟩

private structure ReportWithShape {height depth indexWidth inputWidth allowance radius denominator : ℕ}
    {permutation : Equiv.Perm (Tagged.Row height)}
    {initial : Widths (siteLast height depth indexWidth+1)}
    (entry : CoreBoard.Report permutation depth indexWidth inputWidth allowance radius denominator initial)
    (final : Widths (siteLast height depth indexWidth+1)) where
  report : CoreBoard.Report permutation depth indexWidth inputWidth allowance radius denominator final
  rows_eq : retainedRows report = retainedRows entry
  geometry_eq : retainedGeometry report = retainedGeometry entry

private def replaceVectorLedger {height depth indexWidth inputWidth allowance radius denominator : ℕ}
    {permutation : Equiv.Perm (Tagged.Row height)}
    {initial final : Widths (siteLast height depth indexWidth+1)}
    (entry : CoreBoard.Report permutation depth indexWidth inputWidth allowance radius denominator initial)
    (credit : entry.mount.actual.chordWidths entry.fixed +
      (commodityGraph permutation.symm (siteNumber height depth indexWidth)).chordWidths entry.stock +
      (catalystGraph (siteNumber height depth indexWidth)).chordWidths (fun i => entry.reserved i - entry.used i) = final) :
    ReportWithShape entry final :=
  ⟨{entry with ledger := credit}, rfl, rfl⟩

private def chosenWithShape
    (stable : ∀e,(charges) e=v.wirePaidAt h width bits last chk e)
    (ends : ∀e,0<(charges) e→(live).actual.tail e=(stored).actual.tail e ∧
      (live).actual.head e=(stored).actual.head e) :
    ReportWithShape (sourceReport) (v.wireAt h width bits π last endRam) := by
  let beforeReport := (sourceReport)
  have credit := v.native_terminal_ledger h width size π raw bits horizon age budget small cost state names stable ends
  -- Use the indices recorded by the input report to specialize its ledger update.
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let entry ← Lean.Meta.getFVarFromUserName `beforeReport
      let known ← Lean.Meta.getFVarFromUserName `credit
      let inputType ← Lean.Meta.whnf (← Lean.Meta.inferType entry)
      let outputType ← Lean.Meta.whnf (← goal.getType)
      let input := inputType.getAppArgs
      let finalWidth := outputType.getAppArgs.back!
      let update ← Lean.Meta.mkConstWithFreshMVarLevels ``replaceVectorLedger
      goal.assign (Lean.mkAppN update #[input[0]!,input[2]!,input[3]!,input[4]!,input[5]!,
        input[6]!,input[7]!,input[1]!,input[8]!,finalWidth,entry,known])

attribute [local irreducible] chosenWithShape

local notation "updatedReport" => v.chosenWithShape h width size π raw bits horizon age budget small cost state names

-- Project from the packaged report without copying its dependent indices into the proof.
open Lean Elab Tactic in
local elab "pickShapeField " value:ident " at " field:ident : tactic => withMainContext do
  let record ← Meta.getFVarFromUserName value.getId
  let fields := getStructureFields (← getEnv) ``ReportWithShape
  let some idx := fields.findIdx? (· == field.getId) | throwError "unknown report field {field}"
  (← getMainGoal).assign (mkProj ``ReportWithShape idx record)
  replaceMainGoal []

/-- Change only the proof of the input ledger, leaving original row IDs,
physical socket endpoints, charged signed stocks and original width words
definitionally available to the terminal hardware. -/
def native_state_report
    (stable : ∀e,(charges) e=v.wirePaidAt h width bits last chk e)
    (ends : ∀e,0<(charges) e→(live).actual.tail e=(stored).actual.tail e ∧
      (live).actual.head e=(stored).actual.head e) :
    CoreBoard.Report π.symm D k width (fuel v.mesh*width) v.radius 1 (v.wireAt h width bits π last endRam) := by
  let retained := updatedReport stable ends
  pickShapeField retained at report

/-- The charged width-vector transport preserves the actual numbered row table. -/
theorem native_state_report_rows
    (stable : ∀e,(charges) e=v.wirePaidAt h width bits last chk e)
    (ends : ∀e,0<(charges) e → (live).actual.tail e=(stored).actual.tail e ∧
      (live).actual.head e=(stored).actual.head e) :
    let t:=v.native_state_report h width size π raw bits horizon age budget small cost state names stable ends
    retainedRows t = retainedRows (sourceReport) := by
  let retained := updatedReport stable ends
  pickShapeField retained at rows_eq

/-- The same occurrence geometry is retained together with its dependent row index. -/
theorem native_state_report_geometry
    (stable : ∀e,(charges) e=v.wirePaidAt h width bits last chk e)
    (ends : ∀e,0<(charges) e → (live).actual.tail e=(stored).actual.tail e ∧
      (live).actual.head e=(stored).actual.head e) :
    let t:=v.native_state_report h width size π raw bits horizon age budget small cost state names stable ends
    retainedGeometry t = retainedGeometry (sourceReport) := by
  let retained := updatedReport stable ends
  pickShapeField retained at geometry_eq

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

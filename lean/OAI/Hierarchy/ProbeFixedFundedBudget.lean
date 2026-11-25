import OAI.Hierarchy.ProbeFixedWideFunded
import OAI.Hierarchy.ProbeFixedWideRetainedPrefix
import OAI.Hierarchy.ProbeFixedReadbackProducer
import OAI.Hierarchy.ProbeFixedCalendarReadbacks
import OAI.Hierarchy.ProbeFixedSettledBudget
import OAI.Hierarchy.ProbeFixedSettlementParents

namespace OAI
/-! # Pricing the physical settlement of the accepted signed input -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT ReportSockets PurchaseFrozen
open scoped BigOperators Classical Fin.CommRing

/-- The original pair's used counter after the dated reconciliation scan. -/
def Whole.Reconciliation.usedAt {w r edges n count : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    {core : I → List (Fin edges)} {center : J → List (Fin edges)} {s : Sink r edges}
    {a : ReserveUse.Archive} {reserve : ℕ} {site : Fin n → Fin count} {debit : Fin n → ℕ}
    {e : Fin r ≃ RouteOccurrence core center} {ci : I → ℕ} {keys : J → Fin count} {m : Memory w}
    (_ : Whole.Reconciliation s a reserve site debit e ci keys m) (j : J) : ℕ :=
  RouteSettlement.actual s.banks.used (ReserveUse.output a s.banks reserve site debit m) (keys j).val

namespace FixedProtocolFormat
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
section
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "w" => Native.wordBits h D Native.copies
local notation "stock" => v.fixedTerminalStock P h width
local notation "C" => v.wideSignedChart h width stock
local notation "r" => Fintype.card (Slots h D k)
local notation "s" => v.nativeBoards P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "start" => v.catalystStaticStart P h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "bits" => v.wideSignedPage h width stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "src" => TerminalLayout.source bits
local notation "tab" => TerminalLayout.table bits
local notation "dst" => TerminalLayout.destination bits
local notation "order" => wideRouteOrder h D k
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "route" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
  (directory).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "layout" => FeedLayout.atEvent («N»:=N) v.mesh A (v.nativeFormats P h width) (P).joint.initial width v.keepLimit

/-- The finite original-width profile on the actual funded calendar. The return
on each catalyst edge uses the amount left in its owner's independent counter. -/
def fundedProfile (π : Equiv.Perm (Fin (2^h))) (m : Memory w) (maxBits : ℕ)
    (used : Columns h D × Fin k → ℕ) :
    Catalogue v.sampler π v.depth (v.birthMarks P h width r banks src tab dst owners m) → ℝ :=
  let days := v.birthMarks P h width r banks src tab dst owners m
  let reaches := v.widePaidSlices h width maxBits
  let out := run C (events v.mesh) m
  let ord := (P).catalogue.ordinal v.sampler π v.depth days (v.wideOrder h width) rfl
  let account := v.billedAccount P h width r banks src tab dst owners
  let holdings := (account.read (.outer (v.mesh.inject+v.mesh.cool) 0) out).bits
  let paths := fun i : Commodity (Fin (2^h)) N k => (commodityWalk (S:=v.sampler) π i).map
    (Sum.inl (β:=Bought v.sampler π v.depth days))
  let centers := fun j : Columns h D × Fin k => (catalystWalk (S:=v.sampler) j).map
    (Sum.inl (β:=Bought v.sampler π v.depth days))
  fun e => ((PaidWidths.total reaches out (ord e) + routeLoad paths holdings e +
    routeLoad centers (fun j => fuel v.mesh*width-used j) e : ℕ):ℝ)/width

end

section FundedInvoices
set_option cleanup.letToHave false
set_option maxRecDepth 8192
attribute [local irreducible] CatalystArchive.recordCount CatalystArchive.issued
  CatalystArchive.nativeSite CatalystArchive.debit
  ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec

-- The funding theorem fixes F : Type, and its Commodity routes also live in Type.
open Lean Elab Term in
local elab "nativeSettledBudget" : term => do
  let info ← getConstInfo ``settled_budget
  return mkConst info.name (info.levelParams.map fun _ => Level.zero)

/- The count in the chosen reconciliation is the count of records issued by its
actual date witness. Apply the budget theorem to those same recorded operands. -/
open Lean Elab Term in
local elab "settleRecorded " fn:ident cert:ident orderKeys:ident : term => do
  let budget ← Meta.getFVarFromUserName fn.getId
  let record ← Meta.getFVarFromUserName cert.getId
  let ownerKeys ← Meta.getFVarFromUserName orderKeys.getId
  let recordType ← Meta.whnf (← Meta.inferType record)
  unless recordType.getAppFn.isConstOf ``Whole.Reconciliation do
    throwError "expected the funded reconciliation"
  let #[_, _, _, recordedRouteTypeExpr, _, recordedRoutesExpr, recordedCentersExpr, recordedRowsExpr, recordedCountExpr, _, recordedBookExpr, recordedReserveExpr,
      recordedSiteExpr, _, recordedEnumExpr, recordedPositionExpr, _, recordedArchiveExpr] := recordType.getAppArgs
    | throwError "expected the original reconciliation operands"
  let rowCount ← Meta.whnf recordedRowsExpr
  unless rowCount.getAppFn.isConstOf ``CatalystArchive.recordCount do
    throwError "expected the recorded recordedRowsExpr"
  let issues ← Meta.whnf rowCount.getAppArgs.back!
  unless issues.getAppFn.isConstOf ``CatalystArchive.issued do
    throwError "expected the original dated issues"
  let dates := issues.getAppArgs.back!
  let mut telescope := (← getConstInfo ``CatalystArchive.issued).type
  let mut ledger? : Option Lean.Expr := none
  for arg in issues.getAppArgs do
    let .forallE _ domain body _ := telescope | throwError "unexpected issued-date telescope"
    if domain.getAppFn.isConstOf ``OwnerLedger then
      ledger? := some arg
    telescope := body
  let some ledger := ledger? | throwError "expected the recorded owner ledger"
  -- Reduce the stored and billed date indices when checking this application.
  let result ← Meta.withTransparency .all <| Meta.mkAppOptM' budget #[recordedCountExpr, ledger, dates, ownerKeys, recordedBookExpr, recordedReserveExpr,
    recordedSiteExpr, recordedArchiveExpr, recordedRouteTypeExpr, none, recordedRoutesExpr, recordedCentersExpr, recordedEnumExpr, recordedPositionExpr, record]
  return result

-- Reuse the positive-port theorem on exactly the strip witnesses that created
-- these dates, including their actual chart, initial memory and retained path data.
open Lean Elab Term in
local elab "recordedPositive " cert:ident : term => do
  let record ← Meta.getFVarFromUserName cert.getId
  let recType ← Meta.whnf (← Meta.inferType record)
  unless recType.getAppFn.isConstOf ``Whole.Reconciliation do
    throwError "expected the funded reconciliation"
  let rows ← Meta.whnf (recType.getAppArgs[7]!)
  unless rows.getAppFn.isConstOf ``CatalystArchive.recordCount do
    throwError "expected the funded record count"
  let issues ← Meta.whnf rows.getAppArgs.back!
  unless issues.getAppFn.isConstOf ``CatalystArchive.issued do
    throwError "expected its issued dates"
  let dates ← Meta.withReducible <| Meta.whnf issues.getAppArgs.back!
  unless dates.getAppFn.isConstOf ``StripChart.datesOfStrips do
    throwError "expected dates made from the real mounted strips, found {dates.getAppFn}"
  let positive := Lean.mkConst ``StripChart.datesOfStrips_positive dates.getAppFn.constLevels!
  return mkAppN positive dates.getAppArgs

-- The eight premises have concrete dependent types. Assemble their proof before
-- asking the kernel to check the resulting budget at the theorem's declared type.
open Lean Elab Tactic in
local elab "closeRecordedBudget " value:ident : tactic => withMainContext do
  let proof ← Meta.getFVarFromUserName value.getId
  let goal ← getMainGoal
  goal.assign proof
  replaceMainGoal []

private abbrev FundedInvoiceStatement : Prop :=
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width (small : width ≤ 2^h) (_ : v.widthFloor ≤ width)
      (budget : v.keepLimit*width+1 ≤ 2^h),
      ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (maxBits size : ℕ)
        (extent : v.wideFundedSize h width maxBits ≤ size) (age : v.wideFundedHeight ≤ h)
        (state : Word (Native.wordBits h (2^v.W) Native.copies)),
      let P := v.widePlacement h width
      let G := v.privateArena P h width
      let stock := v.fixedTerminalStock P h width
      let r := Fintype.card (Slots h (2^v.W) k)
      let page := v.wideSignedPage h width stock
      let f := v.nativeBoards P h width
      let cnt := rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger f v.mesh P.catalogue P.routes F G))
      let owners := sinkBank (v.catalystStaticStart P h width) cnt r P.catalogue.rows
      let banks := TerminalLayout.settlement page stock
      let src := TerminalLayout.source page
      let tab := TerminalLayout.table page
      let dst := TerminalLayout.destination page
      let tape := v.wideFundedRaw h width maxBits raw
      let order := wideRouteOrder h (2^v.W) k
      let m := v.wideSignedMidAt h width size stock v.radius π order tape
      let checks := v.wideSignedCheckoutAt h width size stock v.radius π order tape
      let out := run (v.wideSignedChart h width stock) (events v.mesh) m
      let marks := v.birthMarks P h width r banks src tab dst owners m
      let ord := P.catalogue.ordinal v.sampler π v.depth marks (v.wideOrder h width) rfl
      let len := lenCode v.sampler π v.depth marks v.radius
      let paid := Classical.choose_spec (v.wide_funded_run_at h width v.radius π raw maxBits size extent age budget small state)
      checks (G.endAddress v.mesh)=0 →
      (∀e∈events v.mesh, ((v.wideEventSlices h width maxBits e).map
        (fun t => t.toll out (extendedLength ord len) width)).sum ≤ (v.receipts P h width r banks src tab dst owners out e).install) →
      TermBudget p q Q Λ (2^h) width v.radius (∑_j : Columns h (2^v.W)×Fin k,fuel v.mesh*width)
        (scaleOf v.sampler π v.depth marks) (fun e => (len e:ℝ))
        (v.fundedProfile h width π m maxBits
          (Whole.Reconciliation.usedAt (I := Commodity (Fin (2^h)) (Stages h (2^v.W)) k)
            (J := Columns h (2^v.W) × Fin k) paid.1))

set_option maxHeartbeats 8000000 in
/-- The sole price comparison needed here is on the actual emitted slices, at
their original event. All counter identities and all analytic readbacks follow
from the funded execution and its accepted output word. -/
theorem funded_budget_of_invoices : FundedInvoiceStatement v := by
  refine (v.readback_run.and v.calendar_readbacks).mono ?_
  intro h conditions
  obtain ⟨read, analytics⟩ := conditions
  intro width small floor budget π raw maxBits size extent age state P G stock r page f cnt owners banks src tab dst tape
    order m checks out marks ord len paid accepted invoices
  let outerBound := (v.wide_funded_extent h width maxBits).trans extent
  have witnessed := read width small floor budget size outerBound π tape accepted
  obtain ⟨auth⟩ := witnessed
  have accounts := analytics P width r banks src tab dst owners π m m auth
  have whole := auth.nativeStock.mounted_all
  have original := v.wide_signed_boot_at h width size outerBound stock v.radius π order tape auth.endFits
  let parent := v.settlement_parents_original h width r banks src tab dst owners P.joint P.catalogue
    (WideMemory.groups h v.W) (WideMemory.dir h v.W k v.wideJobs) (v.wideSources h width).2
    (v.wideOrder h width) v.radius π m original.2.1 original.2.2.1 (v.wideGeometryPrefix h width).2.2 auth.nativeStock
  let N := Stages h (2^v.W)
  let route := CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
    (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
  let layout := FeedLayout.atEvent (N:=N) v.mesh G (v.nativeFormats P h width) P.joint.initial width v.keepLimit
  let spill := v.paidSpillPath P h width (routeBanks (v.catalystStaticStart P h width) cnt r) route order
  let feeds := v.paidFeedPath P h width route layout
  have word : width < 2^(Native.wordBits h (2^v.W) Native.copies) := small.trans_lt (v.date_prefix_fit h)
  let certificate := paid.1
  let bound := fun {count : ℕ} (ledger : OwnerLedger) =>
    nativeSettledBudget v P h width r banks src tab dst owners m π floor (count := count)
      (fun i => Fin.ext (auth.prices.empty i)) (v.wideOrder h width) rfl spill feeds maxBits ledger
  let ownerKeys := pairKeys (Columns h (2^v.W)) k
  let settled := settleRecorded bound certificate ownerKeys
  let shaped := settled (by
    intro a live
    cases a <;> rfl)
  let originalPorts := recordedPositive certificate
  let ported := shaped originalPorts
  let roomy := ported word
  let accounted := roomy accounts
  let mountedProof := accounted whole
  let archived := mountedProof auth.archives
  let invoiced := archived invoices
  have result := invoiced parent
  closeRecordedBudget result

end FundedInvoices
end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar
end

end OAI

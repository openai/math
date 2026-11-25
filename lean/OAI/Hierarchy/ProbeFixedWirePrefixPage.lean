import OAI.Hierarchy.ProbeFixedWireUsedAt
import OAI.Hierarchy.ProbeFixedWideFundedPrefix

namespace OAI
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart StripDirectory CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open scoped Classical BigOperators Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
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

local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "L" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "C" => v.wideSignedChart h width stock
local notation "supply" => fuel v.mesh*width

local notation "own" => TerminalLayout.ownerArea page stride

local notation "es" => events v.mesh
local notation "pairs" => Columns h D×Fin k

local notation "capPos" => (Nat.mul_pos Fintype.card_pos v.positive : 0 < num)
local notation "flag" => (A).endAddress v.mesh
local notation "base" => v.releasedBase P h width
local notation "keys" => pairKeys (Columns h D) k
local notation "fs" => v.nativeFormats P h width

/-- The reserve replay stamps both lane words at every date, including date
zero. Its used word equals the withdrawals observed in the actual calendar
memory at that date. -/
theorem wire_page_words (initial : Memory w) (runReady : Calendar.mounted C es initial)
    (word : flag<2^w) (pageRoom : 28*2^page<2^w) (widthFits : width<2^w)
    (dates : Dates C initial L base num width)
    {I : Type*} [Fintype I] (paths : I→List (Fin rows)) (centers : pairs→List (Fin rows))
    (ord : Fin r≃RouteOccurrence paths centers) (ci : I→ℕ) (arch : ReserveUse.Archive) (mem : Memory w)
    (R : Whole.Reconciliation sink arch supply (nativeSite L v.mesh (CatalystArchive.issued dates) capPos
      (checkedOut C flag initial)) (debit v.mesh (CatalystArchive.issued dates)) ord ci keys mem)
    (lr : PrefixWidths.Layout num) (out : Memory w)
    (reads : ∀j≤(es).length,∀i : Fin num,
      (out ((PrefixReserve.banks lr old j).used.base+i.val)).val=
        (∑ u : Fin (recordCount v.mesh (CatalystArchive.issued dates)),
          if ((rank v.mesh (CatalystArchive.issued dates)).symm u).1.val < j ∧
            site v.mesh (CatalystArchive.issued dates) u=i then debit v.mesh (CatalystArchive.issued dates) u else 0) ∧
        (out ((PrefixReserve.banks lr old j).reserved.base+i.val)).val=supply)
    (j : ℕ) (date : j≤(es).length) (a : pairs) :
    (out ((PrefixReserve.banks lr old j).used.base+(keys a).val)).val=
      v.wireUsedAt h width j (StockBound.state C initial j) a ∧
    (out ((PrefixReserve.banks lr old j).reserved.base+(keys a).val)).val=supply := by
  have countFits : num<2^w := by
    have room : num≤2^page:=R.usedSize
    omega
  have get:=reads j date (keys a)
  exact ⟨get.1.trans (v.wire_replay_rows h width initial runReady word countFits widthFits dates j date a).symm,get.2⟩

attribute [local irreducible] PhysicalProcedure.Procedure.Exec CatalystArchive.recordCount CatalystArchive.issued
  CatalystArchive.nativeSite CatalystArchive.debit

-- Reuse the exact dates and row enumeration stored in the execution's reconciliation.
-- Reconstructing these dependent arguments by unification unfolds the native program.
open Lean Elab Term in
local elab "fundedPageReport " fn:ident inst:ident cert:ident layout:ident executed:ident observed:ident : term => do
  let f ← Meta.getFVarFromUserName fn.getId
  let commodityInstance ← Meta.getFVarFromUserName inst.getId
  let receipt ← Meta.getFVarFromUserName cert.getId
  let rowLayout ← Meta.getFVarFromUserName layout.getId
  let execution ← Meta.getFVarFromUserName executed.getId
  let readings ← Meta.getFVarFromUserName observed.getId
  let reconciliation ← Meta.whnf (← Meta.inferType receipt)
  unless reconciliation.getAppFn.isConstOf ``Whole.Reconciliation do
    throwError "expected the funded reconciliation"
  let #[_, _, _, commoditiesOperand, _, pathsOperand, centersOperand, rowsOperand, _, _, archiveOperand, _, _, _, orderOperand, keyOperand, _, memoryOperand] :=
    reconciliation.getAppArgs | throwError "unexpected reconciliation inputs"
  let rowCount ← Meta.whnf rowsOperand
  unless rowCount.getAppFn.isConstOf ``CatalystArchive.recordCount do
    throwError "expected dated reserve records"
  let issues ← Meta.whnf rowCount.getAppArgs.back!
  unless issues.getAppFn.isConstOf ``CatalystArchive.issued do
    throwError "expected issued records"
  let result ← Meta.whnf (← Meta.inferType execution)
  unless result.getAppFn.isConstOf ``PhysicalProcedure.Procedure.Exec do
    throwError "expected a prefix execution"
  let output := result.getAppArgs[result.getAppNumArgs - 2]!
  return mkAppN f #[issues.getAppArgs.back!, commoditiesOperand, commodityInstance, pathsOperand, centersOperand, orderOperand, keyOperand,
    archiveOperand, memoryOperand, receipt, rowLayout, output, readings]

/-- Read the original funded execution's two prefix pages directly from the
output memory of the program that writes them. -/
abbrev wide_wire_prefix_page (size bits : ℕ) (extent : v.wideFundedSize h width bits ≤ size)
    (height : v.wideFundedHeight ≤ h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (state : Word w) (maxRows : ℕ)
    (limit : (v.wideReserveLayout h width (v.widePaidSlices h width bits)).scratch+2*max maxRows cnt<2^w)
    (lengths : ∀entry∈v.widePaidSlices h width bits,entry.count ≤ maxRows)
    (widths : ∀e : Fin rows,PaidWidths.total (v.widePaidSlices h width bits)
      (v.wideSignedCheckoutAt h width size stock v.radius π (wideRouteOrder h D k)
        (v.wideFundedRaw h width bits raw)) e<2^w) :=
  let run:=v.wide_funded_prefix_at h width v.radius π raw bits size extent height budget small state maxRows limit lengths widths
  let whole:=(v.wide_funded_stock_at_size h width v.radius π raw bits size extent height budget small).mounted_all
  let word:=(v.wide_stock_sizes h width ((le_max_right ..).trans height) budget small).words.addresses
  let pageRoom:=(v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width)
    ((le_max_left ..).trans height) budget).1
  let initial := v.wideSignedMidAt h width size stock v.radius π (wideRouteOrder h D k)
    (v.wideFundedRaw h width bits raw)
  let _receipt := run.1.1
  let _execution := run.2.1
  let _readings := run.2.2.2.2
  let _rowLayout := v.wideReserveLayout h width ((events v.mesh).flatMap (v.wideEventSlices h width bits))
  let _commodityInstance : Fintype (Commodity (Fin (2^h)) (Stages h (2^v.W)) k) := inferInstance
  let _endpoint := @wire_page_words.{0} F _ k p q Q σ Λ v h width initial whole word pageRoom (small.trans_lt (v.date_prefix_fit h))
  fundedPageReport _endpoint _commodityInstance _receipt _rowLayout _execution _readings

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

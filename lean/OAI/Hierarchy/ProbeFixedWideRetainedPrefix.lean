import OAI.Hierarchy.ProbeFixedWideEventCode
import OAI.Hierarchy.ProbeFixedWidePaidRun
import OAI.Hierarchy.ProbeFixedWidePrefixRecord

namespace OAI
/-! # Original public bytecode of the authenticated paid and reserve control prefix -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StockCommit
open ThreeFlat.RAM PhysicalProcedure
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


attribute [local irreducible] Procedure.Exec CatalystArchive.recordCount CatalystArchive.issued
  CatalystArchive.nativeSite CatalystArchive.debit

/- The record count in a settlement certificate has the form
`recordCount mesh (issued dates)`. Reuse that exact date witness in the prefix program. -/
open Lean Elab Term in
local elab "settlementDates " cert:ident : term => do
  let receipt ← elabTerm cert none
  let recType ← Meta.whnf (← Meta.inferType receipt)
  unless recType.getAppFn.isConstOf ``Whole.Reconciliation do
    throwError "expected a settlement reconciliation"
  let some rows := recType.getAppArgs[7]? | throwError "expected a reconciliation record count"
  let rowCount ← Meta.whnf rows
  unless rowCount.getAppFn.isConstOf ``CatalystArchive.recordCount do
    throwError "expected the native record count"
  let issues ← Meta.whnf rowCount.getAppArgs.back!
  unless issues.getAppFn.isConstOf ``CatalystArchive.issued do
    throwError "expected the dated issues"
  return issues.getAppArgs.back!

/- All arguments to the prefix implication have already been instantiated. Build
its two ordinary applications directly so Lean checks their types together. -/
open Lean Elab Term in
local elab "applySettlement " fn:ident cert:ident ran:ident : term => do
  let implication ← elabTerm fn none
  let record ← elabTerm cert none
  let execution ← elabTerm ran none
  return mkApp2 implication record execution

set_option cleanup.letToHave false in
set_option maxHeartbeats 1000000 in
/-- The real stored paid columns, catalogue, chronological boards and prefix run are
witnessed by one installed execution. Neither a fresh controller nor a per-input choice
of program text enters the statement. -/
abbrev wide_retained_prefix_at :=
  fun (size : ℕ) (extent : (A).endAddress v.mesh ≤ size) (M : ℕ)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (maxBroadcastBits : ℕ)
    (age : v.wideSignedHeight≤h) (small : width≤2^h) (budget : v.keepLimit*width+1≤2^h)
    (state : Word w) (mounted : Calendar.mounted C (events v.mesh)
      (v.wideSignedMidAt h width size stock M π order (v.widePairedWords h width raw))) (maxRows : ℕ)
    (limit : (v.wideReserveLayout h width (v.widePaidSlices h width maxBroadcastBits)).scratch+
        2*max maxRows cnt<2^w)
    (lengths : ∀t∈v.widePaidSlices h width maxBroadcastBits,t.count≤ maxRows)
    (widths : ∀e : Fin (P).catalogue.rows, PaidWidths.total (v.widePaidSlices h width maxBroadcastBits)
      (v.wideSignedCheckoutAt h width size stock M π order (v.widePairedWords h width raw)) e<2^w) =>
    let fixed:=v.wide_paid_run_at h width size extent M π raw maxBroadcastBits age small budget state mounted
    let actual:=Classical.choose_spec fixed
    let header:=v.widePairedWords h width raw
    let paid:=v.wide_paid_mounted_at h width size extent M π raw maxBroadcastBits age budget mounted
    let room:=v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width) age budget
    let certificates := actual.1
    let execution := actual.2.1
    let dates := settlementDates certificates
    let checked := v.wideSignedCheckoutAt h width size stock M π order header
    let board := (P).catalogue.coreMount π (siteNumber h D k) (v.wideOrder h width) checked
    letI : Nonempty (Columns h D) := ⟨.inl ⟨0, Nat.two_pow_pos _⟩⟩
    have accounts : 0 < Fintype.card (Columns h D) * k := Nat.mul_pos Fintype.card_pos v.positive
    let append := v.wide_prefix_from_record h width size M π header (v.wideEventSlices h width maxBroadcastBits)
      (dates := dates) (pos := accounts) (core := board.ordinary) (center := board.centers)
      (enum := CoreRoute.enum board order) (ci := PurchaseInventory.slot) (cj := pairKeys (Columns h D) k)
      extent room.1 mounted paid maxRows limit lengths widths
    let pfx := applySettlement append certificates execution
    And.intro actual pfx

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

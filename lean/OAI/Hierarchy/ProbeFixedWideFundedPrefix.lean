import OAI.Hierarchy.ProbeFixedWideFunded
import OAI.Hierarchy.ProbeFixedWideRetainedPrefix

namespace OAI
/-! # Authenticated selector through the fixed original paid and reserve reporters -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "stock" => v.fixedTerminalStock P h width
local notation "w" => Native.wordBits h D Native.copies
local notation "order" => wideRouteOrder h D k
local notation "C" => v.wideSignedChart h width stock
local notation "page" => v.wideSignedPage h width stock
local notation "banks" => TerminalLayout.settlement page stock
local notation "ss" => v.widePaidSlices h width

local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width)
  v.mesh (P).catalogue (P).routes F A))

section
set_option maxRecDepth 8192
set_option cleanup.letToHave false
set_option maxHeartbeats 2000000

attribute [local irreducible] ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec
  CatalystArchive.recordCount CatalystArchive.issued
  CatalystArchive.nativeSite CatalystArchive.debit

/- Recover the dates from the reconciliation's actual count of issued records. -/
open Lean Elab Term in
local elab "fundedDates " cert:ident : term => do
  let receipt ← Meta.getFVarFromUserName cert.getId
  let reconciliation ← Meta.whnf (← Meta.inferType receipt)
  unless reconciliation.getAppFn.isConstOf ``Whole.Reconciliation do
    throwError "expected a settlement reconciliation"
  let some rows := reconciliation.getAppArgs[7]? | throwError "expected a reconciliation record count"
  let count ← Meta.whnf rows
  unless count.getAppFn.isConstOf ``CatalystArchive.recordCount do
    throwError "expected the native record count"
  let issues ← Meta.whnf count.getAppArgs.back!
  unless issues.getAppFn.isConstOf ``CatalystArchive.issued do
    throwError "expected the dated issues"
  return ← instantiateMVars issues.getAppArgs.back!

private abbrev chosenSettlement {ι : Sort _} {p : ι → Prop} (run : ∃ i, p i) : Prop :=
  p (Classical.choose run)

private abbrev replayConclusion {Record Execution Report : Prop}
    (_ : Record → Execution → Report) : Prop := Report

private theorem forFundedEvents (bits : ℕ) (test : List PaidWidths.Slice → Prop) (paid : test (ss bits)) :
    test ((events v.mesh).flatMap (v.wideEventSlices h width bits)) :=
  (congrArg test (v.wideEventSlices_flat h width bits)).mpr paid

private abbrev fundedRoom (maxRows : ℕ) (slices : List PaidWidths.Slice) : Prop :=
  (v.wideReserveLayout h width slices).scratch + 2 * max maxRows cnt < 2^w

private theorem fundedEventRoom (bits maxRows : ℕ)
    (limit : fundedRoom v h width maxRows (ss bits)) :
    fundedRoom v h width maxRows ((events v.mesh).flatMap (v.wideEventSlices h width bits)) :=
  (congrArg (fundedRoom v h width maxRows) (v.wideEventSlices_flat h width bits)).mpr limit

set_option maxHeartbeats 5000000 in
/-- The funded settlement and the execution, memory frame, width totals and reserve totals
reported by the prefix program for that same settlement. -/
private abbrev fundedPrefixStatement (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
    (raw : Boot.Tape h (2^v.W)) (bits endPos : ℕ) (extendsTape : v.wideFundedSize h width bits ≤ endPos)
    (height : v.wideFundedHeight≤h) (budget : v.keepLimit*width+1≤2^h)
    (small : width≤2^h) (state : Word w) (maxRows : ℕ)
    (limit : fundedRoom v h width maxRows (ss bits))
    (lengths : ∀t∈ss bits,t.count ≤ maxRows)
    (widths : ∀e : Fin (P).catalogue.rows, PaidWidths.total (ss bits)
      (v.wideSignedCheckoutAt h width endPos stock M π order (v.wideFundedRaw h width bits raw)) e<2^w) : Prop :=
  let input := v.wideFundedRaw h width bits raw
  let ran:=v.wide_funded_run_at h width M π raw bits endPos extendsTape height budget small state
  let actual:=Classical.choose_spec ran
  let _certificates := actual.1
  let dates := fundedDates _certificates
  let guard:=(v.wide_funded_stock_at_size h width M π raw bits endPos extendsTape height budget small).mounted_all
  let paid:=v.wide_funded_paid_at_size h width M π raw bits endPos extendsTape height budget small
  let extent:=(v.wide_funded_extent h width bits).trans extendsTape
  let adequate:=v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width) ((le_max_left ..).trans height) budget
  let checkout := v.wideSignedCheckoutAt h width endPos stock M π order input
  let board := (P).catalogue.coreMount π (siteNumber h D k) (v.wideOrder h width) checkout
  let accounts : 0 < Fintype.card (Columns h D)*k :=
    Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨.inl ⟨0, Nat.two_pow_pos _⟩⟩) v.positive
  let eventPaid := forFundedEvents v h width bits
    (fun slices => PaidWidths.Mounted (banks).width (P).catalogue.rows (TerminalLayout.source page)
      slices checkout) paid
  let eventLimit := fundedEventRoom v h width bits maxRows limit
  let eventLengths := forFundedEvents v h width bits
    (fun slices => ∀ t ∈ slices, t.count ≤ maxRows) lengths
  let eventWidths := forFundedEvents v h width bits
    (fun slices => ∀ e : Fin (P).catalogue.rows, PaidWidths.total slices checkout e<2^w) widths
  let append:=v.wide_prefix_from_record h width endPos M π input (v.wideEventSlices h width bits)
    (dates:=dates) (pos:=accounts) (core:=board.ordinary) (center:=board.centers) (enum:=CoreRoute.enum board order)
    (ci:=PurchaseInventory.slot) (cj:=pairKeys (Columns h D) k)
    extent adequate.1 guard eventPaid maxRows eventLimit eventLengths eventWidths
  chosenSettlement ran ∧ replayConclusion append

/- The implication already fixes the program, dates and terminal memory. Apply it to the
two existing receipts directly, as in the retained-prefix proof. -/
open Lean Elab Term in
local elab "fundedReplay " fn:ident cert:ident ran:ident : term => do
  let append ← Meta.getFVarFromUserName fn.getId
  let record ← Meta.getFVarFromUserName cert.getId
  let execution ← Meta.getFVarFromUserName ran.getId
  return mkApp2 append record execution

set_option maxHeartbeats 8000000 in
/-- All preconditions on calendar or repair memory are derived on this finite physical input.
The three remaining scalar estimates concern the size and actual widths of the saved scans. -/
theorem wide_funded_prefix_at (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
    (raw : Boot.Tape h (2^v.W)) (bits endPos : ℕ) (extendsTape : v.wideFundedSize h width bits ≤ endPos)
    (height : v.wideFundedHeight≤h) (budget : v.keepLimit*width+1≤2^h)
    (small : width≤2^h) (state : Word w) (maxRows : ℕ)
    (limit : fundedRoom v h width maxRows (ss bits))
    (lengths : ∀t∈ss bits,t.count ≤ maxRows)
    (widths : ∀e : Fin (P).catalogue.rows, PaidWidths.total (ss bits)
      (v.wideSignedCheckoutAt h width endPos stock M π order (v.wideFundedRaw h width bits raw)) e<2^w) :
    fundedPrefixStatement v h width M π raw bits endPos extendsTape height budget small state
      maxRows limit lengths widths := by
  unfold fundedPrefixStatement
  intro input ran actual certificates dates mounted paid extent adequate checkout board accounts
    eventPaid eventLimit eventLengths eventWidths append
  let execution := actual.2.1
  exact ⟨actual, fundedReplay append certificates execution⟩

theorem wide_funded_prefix (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
    (raw : Boot.Tape h (2^v.W)) (bits : ℕ)
    (height : v.wideFundedHeight≤h) (budget : v.keepLimit*width+1≤2^h)
    (small : width≤2^h) (state : Word w) (maxRows : ℕ)
    (limit : fundedRoom v h width maxRows (ss bits))
    (lengths : ∀t∈ss bits,t.count ≤ maxRows)
    (widths : ∀e : Fin (P).catalogue.rows, PaidWidths.total (ss bits)
      (v.wideSignedCheckoutAt h width (v.wideFundedSize h width bits) stock M π order (v.wideFundedRaw h width bits raw)) e<2^w) :
    fundedPrefixStatement v h width M π raw bits (v.wideFundedSize h width bits) le_rfl height budget small state
      maxRows limit lengths widths :=
  v.wide_funded_prefix_at h width M π raw bits (v.wideFundedSize h width bits) le_rfl height budget small state maxRows
    limit lengths widths

end

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

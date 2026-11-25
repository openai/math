import OAI.Hierarchy.TaggedWireFundedBoundaryData
import OAI.Hierarchy.TaggedWideBranchRoleHeight
import OAI.Hierarchy.TaggedWideNumberedDate

namespace OAI
/-! # Incoming chronological row widths of a selected signed packet -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 3200000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open StripDirectory CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "r" => Fintype.card (Slots h D k)
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "page" => v.wideSignedPage h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "stock" => v.fixedTerminalStock P h width
local notation "bits" => page stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "source" => TerminalLayout.source bits
local notation "table" => TerminalLayout.table bits
local notation "target" => TerminalLayout.destination bits
local notation "C" => v.wideSignedChart h width stock

variable (size : ℕ) (π : Equiv.Perm (Fin (2^h)))
  (seed : Boot.Tape h (2^v.W)) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "es" => events v.mesh
local notation "L" => (reader).format.windows
local notation "base" => v.wideOrigin h width size seed π
local notation "origin" b:arg => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
open Filter CalendarTape RepairHistogram
namespace FundedDate
variable {v h width size π seed age budget small} {tail x} {a : Attempt}
    {t : WireTelescope.CalendarTape.Prefix (v.wideSelector h width age budget small).format.slot (events v.mesh)
      (v.wideOrigin h width size seed π) (.attempt a::tail) x} {c : ((v.wideSelector h width age budget small).format.slot (.attempt a)).choice x}
local notation "rawOf" J:arg => (L).header es (FundedDate.code J) seed

open HistoryRoles
variable (J : v.FundedDate h width size π seed age budget small t c)
    (expanse : v.wideFundedSize h width v.maxBits≤ size)
    (height : v.BranchRoleHeight h width)
local notation "cc" => (P).catalogue
local notation "nativeJ" => origin J.code
local notation "archive" => checkedOut C ((A).endAddress v.mesh) nativeJ
attribute [local irreducible] CatalystArchive.recordCount CatalystArchive.issued
  CatalystArchive.nativeSite CatalystArchive.debit
  ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec

/- Read the dated record family from the reconciliation delivered by the original run. -/
open Lean Elab Term in
private meta def issuedRecordsFrom (receipt : Lean.Ident) : TermElabM Lean.Expr := do
  let evidence ← Meta.getFVarFromUserName receipt.getId
  let reconciliation ← Meta.whnf (← Meta.inferType evidence)
  unless reconciliation.getAppFn.isConstOf ``Whole.Reconciliation do
    throwError "expected the original reserve reconciliation"
  let some count := reconciliation.getAppArgs[7]? | throwError "missing dated record count"
  let rowCount ← Meta.whnf count
  unless rowCount.getAppFn.isConstOf ``CatalystArchive.recordCount do
    throwError "expected a count of dated records"
  let records ← Meta.whnf rowCount.getAppArgs.back!
  unless records.getAppFn.isConstOf ``CatalystArchive.issued do
    throwError "expected issued records"
  return records

open Lean Elab Term in
local elab "recordsOf " receipt:ident : term => issuedRecordsFrom receipt

open Lean Elab Term in
local elab "datesOf " receipt:ident : term => do
  return (← issuedRecordsFrom receipt).getAppArgs.back!

/- Instantiate the generic wire reading with the route family of this reconciliation. -/
open Lean Elab Term in
local elab "atReceipt " fn:ident inst:ident cert:ident : term => do
  let theoremFn ← Meta.getFVarFromUserName fn.getId
  let commodityInstance ← Meta.getFVarFromUserName inst.getId
  let receipt ← Meta.getFVarFromUserName cert.getId
  let reconciliation ← Meta.whnf (← Meta.inferType receipt)
  let #[_, _, _, commodity, _, paths, centers, _, _, _, reserve, _, _, _, ord, ci, _, out] := reconciliation.getAppArgs
    | throwError "expected an original reserve reconciliation"
  return mkAppN theoremFn #[commodity, commodityInstance, paths, centers, ord, ci, reserve, out, receipt]

local notation "num" => Fintype.card (Columns h D)*k
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (PayloadRole (Stages h D) k)) (Fintype.card (PurchasedRole v.depth k)))*2^h
local notation "account" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea bits stride)

private def originalRecords : Attempt → Entry (Fintype.card (Columns h D)*k) width :=
  let witness := v.wide_funded_run_at h width v.radius π.symm (rawOf J) v.maxBits size expanse
    ((le_max_left _ _).trans height.measure) budget small (0 : Word w)
  let _receipt := (Classical.choose_spec witness).1
  recordsOf _receipt

local notation "terms" => originalRecords J expanse height
private def originalDates : Dates C nativeJ account (v.releasedBase P h width) num width :=
  let witness := v.wide_funded_run_at h width v.radius π.symm (rawOf J) v.maxBits size expanse
    ((le_max_left _ _).trans height.measure) budget small (0 : Word w)
  let _receipt := (Classical.choose_spec witness).1
  datesOf _receipt

local notation "releasedTerms" => CatalystArchive.issued (chart := C) (initial := nativeJ) («L» := account)
  («base» := v.releasedBase P h width) (count := num) (payload := width) (originalDates J expanse height)
local notation "marked" => v.birthMarks P h width r banks source table target owners nativeJ
local notation "nativeOrder" => v.wideOrder h width
local notation "cardRows" => v.wide_dated_bought_rows h width
local notation "axis" => pairKeys (Columns h D) k
local notation "names" => timeRows v.sampler π.symm v.depth marked cc nativeOrder cardRows axis
local notation "address" => DatedRows.embed v.sampler π.symm v.depth marked cc nativeOrder cardRows
local notation "directions" => HistoryRoles.sorted v.sampler π.symm v.depth marked
local notation "datedValue" => v.wideDatedValue h width v.maxBits nativeJ archive terms
local notation "ends" => directions ∘ names
local notation "pre" => datedValue J.index.val ∘ address ∘ names

attribute [local irreducible] installedWidths wideDatedValue wideDatedWire wireAt
  HistoryRoles.sorted DatedRows.embed timeRows StockBound.state

set_option maxHeartbeats 6400000 in
private theorem chronological_records (j : Fin ((es).length+1)) :
    installedWidths ends (datedValue j.val ∘ address ∘ names) =
      v.wideDatedWire h width v.maxBits π.symm nativeJ archive terms j.val := by
  let full:=(v.wide_funded_extent h width v.maxBits).trans expanse
  have cover:=max_le_iff.mp (max_le_iff.mp height.report).1
  let originalInput:=v.wideFundedRaw h width v.maxBits (rawOf J)
  have accepted:=(v.wide_verdict h width size full v.radius π.symm originalInput age budget small).mpr J.valid
  let cost:=height.wordRoom size full π.symm originalInput accepted
  let found:=Classical.choose_spec (eventually_atTop.1 v.wide_funded_alignment) h cover.2 width v.maxBits size expanse
    small budget π.symm (rawOf J) (entries := recordCount v.mesh terms)
  let run:=Classical.choose_spec (v.wide_funded_run_at h width v.radius π.symm (rawOf J) v.maxBits size
    expanse cover.1 budget small (0:Word w))
  let _receipt := run.1
  let dates := datesOf _receipt
  have pos : 0 < Fintype.card (Columns h D)*k := Nat.mul_pos Fintype.card_pos v.positive
  have numbered := v.wide_numbered_date h width size π.symm (rawOf J) v.maxBits expanse cover.1 budget small cost
    (dates := dates) (pos := pos) _receipt (found _ _ (fun p=>(axis p).val)) j.val
  exact numbered

set_option maxHeartbeats 6400000 in
private theorem chronological_state (j : Fin ((es).length+1)) :
    v.wireAt h width v.maxBits π.symm j.val (StockBound.state C nativeJ j.val) =
      v.wideDatedWire h width v.maxBits π.symm nativeJ archive releasedTerms j.val := by
  let full := (v.wide_funded_extent h width v.maxBits).trans expanse
  have cover := max_le_iff.mp (max_le_iff.mp height.report).1
  let originalInput := v.wideFundedRaw h width v.maxBits (rawOf J)
  let run:=Classical.choose_spec (v.wide_funded_run_at h width v.radius π.symm (rawOf J) v.maxBits size
    expanse cover.1 budget small (0:Word w))
  let _receipt := run.1
  let dates := originalDates J expanse height
  let active := (v.wide_funded_stock_at_size h width v.radius π.symm (rawOf J) v.maxBits size expanse
    cover.1 budget small).mounted_all
  let word := (v.wide_stock_sizes h width age budget small).words.addresses
  let pageRoom := (v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width)
    ((le_max_left ..).trans cover.1) budget).1
  let paid := Classical.choose_spec (eventually_atTop.1 v.wide_wire_paid) h
    ((le_max_left _ _).trans ((le_max_right _ _).trans height.measure)) width small budget size full π.symm
    originalInput v.maxBits
  let measured := Classical.choose_spec (eventually_atTop.1 v.wire_paid_ends) h
    ((le_max_right _ _).trans ((le_max_right _ _).trans height.measure)) width small budget size full π.symm
    originalInput v.maxBits
  let _generic := @dated_wire_of_run.{0} F _ k p q Q σ Λ v h width v.maxBits π.symm nativeJ active word
    pageRoom (small.trans_lt (v.date_prefix_fit h)) dates
  let _commodities : Fintype (Commodity (Fin (2^h)) (Stages h D) k) := inferInstance
  have observed := (atReceipt _generic _commodities _receipt) paid.1 measured j.val (Nat.lt_succ_iff.mp j.isLt)
  exact observed

private theorem sameIssuedEntries {bitsCount channelCount portCount capacity packetWidth : ℕ}
    {calendar : Chart bitsCount channelCount portCount} {firstMemory secondMemory : Memory bitsCount}
    {firstLedger secondLedger : OwnerLedger} {firstBase secondBase : Event → ℕ}
    (firstHistory : Dates calendar firstMemory firstLedger firstBase capacity packetWidth)
    (secondHistory : Dates calendar secondMemory secondLedger secondBase capacity packetWidth)
    (agreement : ∀ a present, (firstHistory a present).entry = (secondHistory a present).entry) :
    CatalystArchive.issued (chart := calendar) (initial := firstMemory) («L» := firstLedger)
      («base» := firstBase) (count := capacity) (payload := packetWidth) firstHistory =
    CatalystArchive.issued (chart := calendar) (initial := secondMemory) («L» := secondLedger)
      («base» := secondBase) (count := capacity) (payload := packetWidth) secondHistory := by
  funext event
  by_cases hMem : Event.attempt event ∈ events calendar.mesh
  · simpa only [CatalystArchive.issued, dite_eq_left hMem] using agreement event hMem
  · simp only [CatalystArchive.issued, dite_eq_right hMem]

private theorem original_records_at_release : releasedTerms = terms := by
  unfold originalRecords
  apply sameIssuedEntries
  intro event scheduled
  rfl

/-- The original issued table numbers all paid rows, goods and reserve axes at every
boundary of the same realized tape. Distinct parallel rows keep their native ordinals. -/
theorem signed_chronological_width (j : Fin ((es).length+1)) :
    installedWidths ends (datedValue j.val ∘ address ∘ names)=
      v.wireAt h width v.maxBits π.symm j.val (StockBound.state C nativeJ j.val) := by
  have same := congrArg (fun values => v.wideDatedWire h width v.maxBits π.symm nativeJ archive values j.val)
    (original_records_at_release J expanse height)
  exact (chronological_records J expanse height j).trans (same.symm.trans (chronological_state J expanse height j).symm)

theorem signed_input_numbered :
    installedWidths ends pre=v.wideCursorWidth h width size π seed age budget small t :=
  (J.signed_chronological_width expanse height J.index.castSucc).trans
    (J.before_graph ((v.wide_funded_extent h width v.maxBits).trans expanse) height.replay).symm

theorem signed_output_numbered :
    installedWidths ends (datedValue (J.index.val+1) ∘ address ∘ names)=
      v.wideCursorWidth h width size π seed age budget small (t.advance c) := by
  refine (J.signed_chronological_width expanse height J.index.succ).trans ?_
  change v.wireAt h width v.maxBits π.symm (J.prior.length+1)
    (StockBound.state C nativeJ (J.prior.length+1))=_
  rw [J.next_state]
  exact (J.next_graph ((v.wide_funded_extent h width v.maxBits).trans expanse) height.replay).symm

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

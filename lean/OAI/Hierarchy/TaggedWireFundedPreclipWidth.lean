import OAI.Hierarchy.TaggedWireReportedPath
import OAI.Hierarchy.TaggedWideRoleMaskSlots
import OAI.Hierarchy.TaggedWireMiddleRoleLayout
import OAI.Hierarchy.TaggedWireFundedMiddleReplay
import OAI.Hierarchy.TaggedWireNumberedPreclip
import OAI.Hierarchy.TaggedWireFundedSpillAmount
import OAI.Hierarchy.ProbeFixedWideSpillRolePages

namespace OAI
/-! # The actual corrected width sheet is the signed operator’s intermediate state -/

noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
set_option cleanup.letToHave false
-- These fully specialized site statements take excessive time in the premise suggestion index.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "preclip_indexed_site"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "preclip_indexed_range"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "preclip_published"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "numbered_spill_only"

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
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


local notation "page" => v.wideSignedPage h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "f" => v.nativeFormats P h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "bits" => page stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "source" => TerminalLayout.source bits
local notation "table" => TerminalLayout.table bits
local notation "target" => TerminalLayout.destination bits
local notation "C" => v.wideSignedChart h width stock
local notation "g" => v.stamp P h width r banks source table target owners
local notation "order" => wideRouteOrder h D k


variable (size : ℕ) (extent : (A).endAddress v.mesh≤ size) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
  (seed : Boot.Tape h D) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "es" => events v.mesh
local notation "L" => (reader).format.windows
local notation "mid" => v.wideSignedMidAt h width size stock M π order

local notation "funded" => v.wideFundedRaw h width v.maxBits seed
local notation "original" => v.wideSignedWords h width stock v.radius π.symm order funded
local notation "V" => v.catalystMarkets P h width
local notation "dims" => v.wide_stock_sizes h width age budget small
local notation "base" => v.wideOrigin h width size seed π
local notation "origin" b:arg => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
local notation "auth" => v.wide_signed_words_authentic h width stock v.radius π.symm order funded
local notation "heap" => (v.wideGeometryPrefix h width).2.1

open Filter CalendarTape RepairHistogram HistoryRoles.RoleProgram ProtocolRAMEmit
open LinearAlgebra.SpectralBooks ChordGraph
namespace FundedDate
variable {v h width size π seed age budget small} {tail x} {a : Attempt}
    {t : WireTelescope.CalendarTape.Prefix slots es base (.attempt a::tail) x} {c : (slots (.attempt a)).choice x}
    (H : v.FundedDate h width size π seed age budget small t c)
local notation "ev" => Event.attempt a
local notation "u" => (es).length-(ev::tail).length
local notation "native" => origin H.code
local notation "tape" => v.wideFundedRaw h width v.maxBits ((L).header es H.code seed)
local notation "entry" => run C H.prior native
local notation "out" => after C ev entry
local notation "t₀" => v.taskCommit P h width a
local notation "st" => v.stage P h width r banks source table target owners a entry
local notation "tag" => RepairHistogram.kind («goods»:=(t₀).goods) (t₀).plan.bank (t₀).columns st
local notation "o" => v.nativeSlots P h width a
local notation "inputGoods" => fun i=>v.wireGoodsAt h width u x ((o).symm i)
local notation "ar" => ((f) a).pricedArea
local notation "axes" => Columns h D×Fin k
local notation "supply" => fuel v.mesh*width
local notation "origReserve" => fun pair=>supply-v.wireUsedAt h width u x pair

local notation "place" => siteNumber h D k
local notation "paid0" => v.wirePaidAt h width v.maxBits u x
local notation "oldMount" => (P).catalogue.coreMount π.symm place (v.wideOrder h width) x
local notation "afterValue" => Sum.elim H.afterPaid (Sum.elim (H.afterGoods ∘ o) H.nextReserve)
local notation "leftover" => fun z=>(origReserve) z-H.reserveDebit z
local notation "carry" => (oldMount).actual.chordWidths paid0+H.afterMount.actual.chordWidths H.paid+
  (catalystGraph place).chordWidths leftover
local notation "cap" => (show FeedTransfer.Transfer h D k from
  ⟨fun _=>0,fun i=>H.afterGoods ((o) i)+H.spill ((o) i),fun _=>0,fun i=>H.afterGoods ((o) i),
    fun i=>H.spill ((o) i),fun _=>by simp⟩)

local notation "rawOf" J:arg => (L).header es (FundedDate.code J) seed
attribute [local irreducible] wideDatedValue StockBound.state

open Lean Elab Term in
local elab "preclipEntriesOf" evidence:ident : term => do
  let proof ← Meta.getFVarFromUserName evidence.getId
  let equation ← Meta.whnf (← Meta.inferType proof)
  let some (_, left, _) := equation.eq? | throwError "expected the original dated amount equation"
  unless left.getAppFn.isConstOf ``wideDatedValue do throwError "expected the original dated values"
  let app := left.getAppArgs
  return app[app.size - 2]!

/-- The numbered rows come from the issued entries of this funded run. -/
private def preclipEntriesAt (rawTape : Boot.Tape h D) (expense : v.wideFundedSize h width v.maxBits ≤ size)
    (heightProof : v.wideDatedLedgerHeight ≤ h) (sizeRoom : width ≤ 2^h)
    (creditRoom : v.keepLimit*width+1 ≤ 2^h) (startWord : Word w) : Attempt → Entry num width :=
  let _date := v.wide_dated_amounts h width size π.symm rawTape expense heightProof sizeRoom creditRoom startWord 0 (Nat.zero_le _)
  preclipEntriesOf _date


open HistoryRoles
variable (J : v.FundedDate h width size π seed age budget small t c)
    (expanse : v.wideFundedSize h width v.maxBits≤ size)
    (ledgerAge : v.wideDatedLedgerHeight≤h) (reportAge : v.reportHeight≤h)
    (paidAge : v.paidBallotHeight≤h) (word : v.ReportWordRoom h width)
    (first : ℕ) (input : Fin (es).length→Memory w)
local notation "cc" => (P).catalogue
local notation "nativeJ" => origin J.code
local notation "archive" => checkedOut C ((A).endAddress v.mesh) nativeJ
local notation "terms" => preclipEntriesAt (v:=v) (h:=h) (width:=width) (size:=size) (π:=π) (rawOf J) expanse ledgerAge small budget (0 : Word w)
local notation "marked" => v.birthMarks P h width r banks source table target owners nativeJ
local notation "nativeOrder" => v.wideOrder h width
local notation "cardRows" => v.wide_dated_bought_rows h width
local notation "axis" => pairKeys (Columns h D) k
local notation "names" => timeRows v.sampler π.symm v.depth marked cc nativeOrder cardRows axis
local notation "address" => DatedRows.embed v.sampler π.symm v.depth marked cc nativeOrder cardRows
local notation "directions" => HistoryRoles.sorted v.sampler π.symm v.depth marked
local notation "correctedWidths" => v.wideCorrectedWidths h width size v.radius π.symm (rawOf J) v.maxBits terms first input
local notation "clip" => fun i=>RouteSettlement.actual (v.wideSpillPage h width v.maxBits first J.index.val).overflow
  (input J.index) (PurchaseInventory.slot i)

attribute [local irreducible] CatalystArchive.recordCount CatalystArchive.issued CatalystArchive.nativeSite CatalystArchive.debit

attribute [local irreducible] wide_report_for_dates wideSignedMidAt checkedOut

/- Reuse the actual native reconciliation and its funded date alignment. -/
open Lean Elab Term in
local elab "numberedFromReport " sourceReceipt:ident dayValue:ident spillData:ident : term => do
  let nativeProof ← Meta.getFVarFromUserName sourceReceipt.getId
  let applied ← Meta.whnf nativeProof
  unless applied.getAppFn.isConstOf ``wide_report_for_dates do
    throwError "expected the report from the reconciled dates; got {applied.getAppFn.constName?}"
  let theoremHead := Lean.mkConst ``wide_numbered_preclip applied.getAppFn.constLevels!
  let day ← Meta.getFVarFromUserName dayValue.getId
  let spill ← Meta.getFVarFromUserName spillData.getId
  return mkApp2 (mkAppN theoremHead applied.getAppArgs) day spill

include reportAge word in
private theorem fundedNumberedMiddleAt (j : ℕ) (spillValues : Goods h v.W k → ℕ) :
    let boardMount := (cc).coreMount π.symm place nativeOrder archive
    let transaction := FeedTransfer.middleAmounts boardMount (v.wideDatedValue h width v.maxBits nativeJ archive terms j) spillValues
    installedWidths (directions ∘ names) (transaction ∘ address ∘ names) =
      FeedTransfer.amountsWidth boardMount transaction := by
  let extent:=(v.wide_funded_extent h width v.maxBits).trans expanse
  have caps:=max_le_iff.mp (max_le_iff.mp reportAge).1
  let tapeJ:=v.wideFundedRaw h width v.maxBits (rawOf J)
  have accepted:=(v.wide_verdict h width size extent v.radius π.symm tapeJ age budget small).mpr J.valid
  let cost:=word size extent π.symm tapeJ accepted
  let found {countRows : ℕ} (readSite : Fin countRows → Fin num) (readFee : Fin countRows → ℕ) := Classical.choose_spec (eventually_atTop.1 v.wide_funded_alignment) h caps.2 width v.maxBits size expanse
    small budget π.symm (rawOf J) readSite readFee (fun row => (axis row).val)
  let nativeReport := v.wide_native_report h width size π.symm (rawOf J) v.maxBits expanse caps.1 budget small cost (0 : Word w) found
  let certified := numberedFromReport nativeReport j spillValues
  run_tac
    let dateGoal ← Lean.Elab.Tactic.getMainGoal
    dateGoal.withContext do
      let nativeLaw ← Lean.Meta.getFVarFromUserName `certified
      -- The numbered equation uses the same issued dates after unfolding the checkout.
      dateGoal.assign nativeLaw
      Lean.Elab.Tactic.replaceMainGoal []


private theorem preclipWidthTransition {Amount State Spill Width : Type}
    (record : Amount → Width) (middle : State → Spill → Amount) (physical : Amount → Width)
    {displayed : Amount} {before afterState : State} {atSpill terminalSpill : Spill}
    {intermediate targetWidth : Width}
    (issued : displayed = middle before atSpill)
    (numbered : record (middle before atSpill) = physical (middle before atSpill))
    (values : afterState = before) (spillRead : atSpill = terminalSpill)
    (mount : physical (middle afterState terminalSpill) = intermediate)
    (settled : intermediate = targetWidth) : record displayed = targetWidth := by
  cases issued
  cases values
  cases spillRead
  exact numbered.trans (mount.trans settled)

include reportAge paidAge word in
/-- No reordering of parallel original rows: the bit width indexed by each original date,
row and side is the one fed to the genuine signed-before-spill state. -/
theorem indexed_middle_width (archived : ∀addressIndex<(A).endAddress v.mesh,input J.index addressIndex=archive addressIndex) :
    installedWidths (directions ∘ names) ((correctedWidths 0 J.index.succ) ∘ address ∘ names)=
      FeedTransfer.input (π:=π.symm) («place»:=place) carry cap := by
  let extent := (v.wide_funded_extent h width v.maxBits).trans expanse
  have caps := max_le_iff.mp (max_le_iff.mp reportAge).1
  have numbered := fundedNumberedMiddleAt J expanse ledgerAge reportAge word (J.prior.length+1) clip
  let valuation := v.wideDatedValue h width v.maxBits nativeJ archive terms
  have values : afterValue = valuation (J.prior.length + 1) :=
    (H.middle_replay J expanse ledgerAge paidAge (0:Word w)).trans (congrArg valuation J.clock.2)
  have flow : clip=J.spill ∘ o :=
    funext (J.spill_page v.maxBits first J.index J.index_event (input J.index) archived)
  have firstEq : correctedWidths 0 J.index.succ=FeedTransfer.middleAmounts
      ((cc).coreMount π.symm place nativeOrder archive)
      (v.wideDatedValue h width v.maxBits nativeJ archive terms (J.prior.length+1)) clip:=by
    simp only [wideCorrectedWidths, Fin.cases_succ, ite_true]
    rfl
  let mounted := (cc).coreMount π.symm place nativeOrder archive
  exact preclipWidthTransition
    (fun amounts => installedWidths (directions ∘ names) (amounts ∘ address ∘ names))
    (FeedTransfer.middleAmounts mounted) (FeedTransfer.amountsWidth mounted)
    firstEq numbered values flow (H.middle_mount J extent paidAge) (H.middle_width extent paidAge expanse caps.1)

local notation "rows" => (correctedWidths 0 J.index.succ) ∘ address ∘ names
local notation "bound" => FeedTransfer.input (π:=π.symm) («place»:=place) carry cap
variable (archived : ∀addressIndex<(A).endAddress v.mesh,input J.index addressIndex=archive addressIndex)
    (unique : Exclusive marked) (capacity : Public v.sampler h v.W k v.wideJobs→ℕ)
    (fit : ∀i side,(rows) i≤capacity (named v.sampler π.symm v.depth marked unique names (i,side)))
    {length : ℕ} (within : ∀portName,capacity portName≤length)
local notation "actualWidthEq" => H.indexed_middle_width J expanse ledgerAge reportAge paidAge word first input archived
local notation "stateEmbedding" => statePlace v.sampler π.symm v.depth marked unique names rows capacity fit
local notation "roleDirectory" => LedgerStep.rolesChart capacity within (shelfSlot v.sampler)

/-- The same local role and digit used by the native correction page, on the actual intermediate
domain of the signed step. The three dates named by H, J and the original checkout may differ
outside their observed private prefix. -/
def preclip_indexed_layout :=
  placedMiddle v.sampler π.symm v.depth marked unique names rows capacity fit within actualWidthEq

local notation "layout" => H.preclip_indexed_layout J expanse ledgerAge reportAge paidAge word first input
  archived unique capacity fit within

theorem preclip_indexed_site (siteId : Fin (siteLast h D k+1)) (z : SiteBit bound siteId) :
    (layout ⟨siteId,z⟩).1=siteId :=
  placedMiddle_site v.sampler π.symm v.depth marked unique names rows capacity fit within actualWidthEq siteId z

theorem preclip_indexed_range : Set.range layout=Set.range ((stateEmbedding).trans roleDirectory) :=
  placedMiddle_range v.sampler π.symm v.depth marked unique names rows capacity fit within actualWidthEq

/-- A native returned width word recognizes precisely the physical signed intermediate
cells, including the blank socket numbers. All projections use the same CPU memory. -/
theorem preclip_published (wordFits : ∀portName,capacity portName<2^w) (oldCount roleStart : ℕ) (outWord : Memory w)
    (ids : Fin (Fintype.card (HistoryRoles.Source v.sampler π.symm v.depth marked))→ℕ)
    (record : DatedRoleSheets.roleFact oldCount v.sampler π.symm v.depth marked unique names
      roleStart rows ids outWord 0) (site : Fin (siteLast h D k+1))
    (cell : Fin (HistoryRoles.stride k v.sampler.degree v.wideJobs*length)) :
    (site,cell)∈Set.range layout ↔ (finProdFinEquiv.symm cell).2.val<
      (outWord (roleStart+1+(finProdFinEquiv (site,(finProdFinEquiv.symm cell).1)).val)).val := by
  rw [H.preclip_indexed_range J expanse ledgerAge reportAge paidAge word first input archived unique capacity fit within]
  exact DatedRoleSheets.dense_range v.sampler π.symm v.depth marked unique names rows ids capacity fit length within
    (fun i=>(fit i false).trans_lt (wordFits _)) oldCount roleStart outWord record site cell

/-- The endogenous birth marks on this original continuation are exclusive. -/
theorem preclipUnique : Exclusive marked := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  apply v.paid_days_exclusive

/-- A capacity check per original role and side for this corrected width file. -/
abbrev preclipCapFit (capAt : Public v.sampler h v.W k v.wideJobs→ℕ) : Prop :=
  ∀i side,(rows) i≤capAt (named v.sampler π.symm v.depth marked J.preclipUnique names (i,side))

/-- A physical corrected sector with its time and source code visible for
transport from the completed selected path. -/
abbrev preclipRoleFileAt (code : Bits (CalendarTape.bits slots es)) (day : Fin (es).length)
    (startWord : ℕ) (output : Memory w) : Prop :=
  let rawTape:=(L).header es code seed
  let runMid:=origin code
  let calendarMarks:=v.birthMarks P h width r banks source table (TerminalLayout.destination bits) owners runMid
  let exclusiveAt : Exclusive calendarMarks := by
    let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
    apply v.paid_days_exclusive
  let scannedEntries := preclipEntriesAt (v:=v) (h:=h) (width:=width) (size:=size) (π:=π) rawTape expanse ledgerAge small budget (0 : Word w)
  let numberedOrder:=v.wideOrder h width
  let namedRows:=timeRows v.sampler π.symm v.depth calendarMarks cc numberedOrder cardRows axis
  let ordinalEmbed:=DatedRows.embed v.sampler π.symm v.depth calendarMarks cc numberedOrder cardRows
  let widthAtDay:=v.wideCorrectedWidths h width size v.radius π.symm rawTape v.maxBits scannedEntries first input
  let originalCodes:=sparseKey v.sampler π.symm v.depth calendarMarks cc numberedOrder cardRows (PurchaseInventory.slotEquiv h N k) axis
  DatedRoleSheets.roleFact (Fintype.card (RoleProgram.Old h v.W k (cc).rows)) v.sampler π.symm v.depth calendarMarks exclusiveAt namedRows
    startWord (widthAtDay 0 day.succ ∘ ordinalEmbed ∘ namedRows) (fun i=>(originalCodes (namedRows i)).val) output 0

abbrev preclipRoleFact (startWord : ℕ) (output : Memory w) : Prop :=
  preclipRoleFileAt (v:=v) (h:=h) (width:=width) (size:=size) (π:=π) (seed:=seed)
    (age:=age) (budget:=budget) (small:=small) expanse ledgerAge first input J.code J.index startWord output


private theorem preclipSplitChordWidths {edge : Type} [Fintype edge] {countSites : ℕ}
    (G : PortGraph (Fin countSites) edge) (keptWidths : Widths countSites) (goods spill : edge → ℕ) :
    (keptWidths+G.chordWidths (fun _ => 0))+G.chordWidths (fun i => goods i+spill i) =
      (keptWidths+G.chordWidths goods)+G.chordWidths spill := by
  simp only [chordWidths_empty, add_zero, chordWidths_add, add_assoc]

include reportAge paidAge word archived in
/-- The corrected successor row before clipping consists of the retained
stock and one more copy of the commodity bits whose original walk is rerouted. -/
theorem numbered_spill_only (day : Fin (es).length) (onDate : (es).get day=.attempt a)
    (pruned : Memory w) (retained : ∀n<(A).endAddress v.mesh,pruned n=archive n) :
    installedWidths (directions ∘ names) rows=
      (carry+(commodityGraph π.symm place).chordWidths (H.afterGoods ∘ o))+
        (commodityGraph π.symm place).chordWidths (fun i=>
          RouteSettlement.actual (v.wideSpillPage h width v.maxBits first day.val).overflow pruned
            (PurchaseInventory.slot i)) := by
  have amounts :
      (fun i=>RouteSettlement.actual (v.wideSpillPage h width v.maxBits first day.val).overflow pruned
        (PurchaseInventory.slot i))=H.spill ∘ o := by
    funext i
    exact (J.spill_page v.maxBits first day onDate pruned retained i).trans
      (congrFun (H.spill_replay J) ((o) i)).symm
  refine (H.indexed_middle_width J expanse ledgerAge reportAge paidAge word first input archived).trans ?_
  refine Eq.trans ?_ (congrArg (fun spillVals => (carry+(commodityGraph π.symm place).chordWidths (H.afterGoods ∘ o))+(commodityGraph π.symm place).chordWidths spillVals) amounts.symm)
  exact preclipSplitChordWidths (commodityGraph π.symm place) carry (H.afterGoods ∘ o) (H.spill ∘ o)


end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

import OAI.Hierarchy.ProbePaidChordWeights
import OAI.Hierarchy.ProbeFixedWirePaidEnds
import OAI.Hierarchy.ProbeFixedWideDatedAmounts

namespace OAI
/-! # The three dated financial rows on the original signed graph -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
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

local notation "place" => siteNumber h D k
local notation "mountAt" => fun π m=>(P).catalogue.coreMount π place (v.wideOrder h width) m
local notation "order" => wideRouteOrder h D k
open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor

/-- The physical graph formed from the paid, held and reserve components of
the dated role vector, with the paid endpoints read at checkout. -/
def wideDatedWire (bits : ℕ) (π : Equiv.Perm (Fin (2^h))) (initial archive : Memory w)
    (issues : Attempt→Entry num width) (j : ℕ) :=
  let value:=v.wideDatedValue h width bits initial archive issues j
  (mountAt π archive).actual.chordWidths (fun e=>value (.inl e))+
    (commodityGraph (k:=k) π place).chordWidths (fun i=>value (.inr (.inl i)))+
    (catalystGraph place).chordWidths (fun a=>value (.inr (.inr a)))

/-- Original source rows of the paid, held, and reserved widths. Keeping the
original row index preserves all parallel catalogue edges individually. -/
theorem dated_amounts_of_run (bits : ℕ) (initial : Memory w)
    (live : Calendar.mounted C es initial) (word : flag<2^w) (pageFit : 28*2^page<2^w) (widthFit : width<2^w)
    (dates : Dates C initial L base num width)
    {I : Type*} [Fintype I] (paths : I→List (Fin rows)) (centers : pairs→List (Fin rows))
    (ord : Fin r≃RouteOccurrence paths centers) (ci : I→ℕ) (arch : ReserveUse.Archive) (out : Memory w)
    (reconciled : Whole.Reconciliation sink arch supply (nativeSite L v.mesh (CatalystArchive.issued dates)
      capPos (checkedOut C flag initial)) (debit v.mesh (CatalystArchive.issued dates)) ord ci keys out)
    (cash : ∀j≤(es).length,∀e,v.wirePaidAt h width bits j (StockBound.state C initial j) e=
      v.wirePaidAt h width bits j (checkedOut C flag initial) e)
    : ∀j≤(es).length,v.wideDatedValue h width bits initial (checkedOut C flag initial) (CatalystArchive.issued dates) j=
      Sum.elim (v.wirePaidAt h width bits j (StockBound.state C initial j))
        (Sum.elim (v.wireGoodsAt h width j (StockBound.state C initial j))
          (fun a=>supply-v.wireUsedAt h width j (StockBound.state C initial j) a)) := by
  intro j last
  have number : num<2^w:=by
    have fit : num≤2^page:=reconciled.usedSize
    omega
  funext sourceRow
  rcases sourceRow with e|i|a
  · exact (cash j last e).symm
  · exact (v.wire_goods_run h width j initial i).symm
  · exact congrArg (fun n=>supply-n)
      (v.wire_countAt h width initial live word number widthFit dates j last a).symm

/-- A certified original row history can be used directly, with the chosen
dates extracted from the settlement's actual reconciliation. -/
theorem dated_wire_of_run (bits : ℕ) (π : Equiv.Perm (Fin (2^h))) (initial : Memory w)
    (live : Calendar.mounted C es initial) (word : flag<2^w) (pageFit : 28*2^page<2^w) (widthFit : width<2^w)
    (dates : Dates C initial L base num width)
    {I : Type*} [Fintype I] (paths : I→List (Fin rows)) (centers : pairs→List (Fin rows))
    (ord : Fin r≃RouteOccurrence paths centers) (ci : I→ℕ) (arch : ReserveUse.Archive) (out : Memory w)
    (reconciled : Whole.Reconciliation sink arch supply (nativeSite L v.mesh (CatalystArchive.issued dates)
      capPos (checkedOut C flag initial)) (debit v.mesh (CatalystArchive.issued dates)) ord ci keys out)
    (cash : ∀j≤(es).length,∀e,v.wirePaidAt h width bits j (StockBound.state C initial j) e=
      v.wirePaidAt h width bits j (checkedOut C flag initial) e)
    (ends : ∀j≤(es).length,∀e,0<v.wirePaidAt h width bits j (StockBound.state C initial j) e→
      (mountAt π (StockBound.state C initial j)).actual.tail e=(mountAt π (checkedOut C flag initial)).actual.tail e ∧
      (mountAt π (StockBound.state C initial j)).actual.head e=(mountAt π (checkedOut C flag initial)).actual.head e) :
    ∀j≤(es).length,v.wireAt h width bits π j (StockBound.state C initial j)=
      v.wideDatedWire h width bits π initial (checkedOut C flag initial) (CatalystArchive.issued dates) j := by
  intro j last
  have fields:=v.dated_amounts_of_run h width bits initial live word pageFit widthFit
    dates paths centers ord ci arch out reconciled cash j last
  have paid:=positive_chords (mountAt π (StockBound.state C initial j)).actual
    (mountAt π (checkedOut C flag initial)).actual _ (ends j last)
  unfold wireAt wideDatedWire
  rw [fields]
  exact congrArg (fun z => z + _ + _) paid

/-- A single public threshold covers the measured weights and the dated
endpoint reads, for every permutation and every original selector tape. -/
def wideDatedLedgerHeight :=
  max v.wideFundedHeight (max (Classical.choose (Filter.eventually_atTop.1 v.wide_wire_paid))
    (Classical.choose (Filter.eventually_atTop.1 v.wire_paid_ends)))

attribute [local irreducible] CatalystArchive.recordCount CatalystArchive.issued
  CatalystArchive.nativeSite CatalystArchive.debit
  ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec

/- Specialize a dated ledger theorem to the routes and dates recorded by a funded run. -/
open Lean Elab Term in
local elab "withDatedReceipt " fn:ident inst:ident cert:ident : term => do
  let theoremFn ← Meta.getFVarFromUserName fn.getId
  let commodityInstance ← Meta.getFVarFromUserName inst.getId
  let receipt ← Meta.getFVarFromUserName cert.getId
  let reconciliation ← Meta.whnf (← Meta.inferType receipt)
  unless reconciliation.getAppFn.isConstOf ``Whole.Reconciliation do
    throwError "expected a reserve reconciliation"
  let #[_, _, _, commodityOperand, _, pathsOperand, centersOperand, countOperand, _, _, archiveOperand, _, _, _, ordOperand, ciOperand, _, outOperand] := reconciliation.getAppArgs
    | throwError "unexpected reconciliation arguments"
  let rowCount ← Meta.whnf countOperand
  unless rowCount.getAppFn.isConstOf ``CatalystArchive.recordCount do
    throwError "expected a count of dated records"
  let issued ← Meta.whnf rowCount.getAppArgs.back!
  unless issued.getAppFn.isConstOf ``CatalystArchive.issued do
    throwError "expected the issued records"
  let dates := issued.getAppArgs.back!
  return mkAppN theoremFn #[dates, commodityOperand, commodityInstance, pathsOperand, centersOperand, ordOperand, ciOperand, archiveOperand, outOperand, receipt]

/-- Exact three-component equality for the particular dates chosen by the
real funded settlement. This applies to every intermediate cut, including
the two boundary cuts. -/
abbrev wide_dated_wire (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
    (extent : v.wideFundedSize h width v.maxBits≤ size) (height : v.wideDatedLedgerHeight≤h)
    (small : width≤2^h) (budget : v.keepLimit*width+1≤2^h) (state : Word w) :=
  let tape:=v.wideFundedRaw h width v.maxBits raw
  let enough:= (v.wide_funded_extent h width v.maxBits).trans extent
  let age:= (le_max_left _ _).trans height
  let paid:=Classical.choose_spec (v.wide_funded_run_at h width v.radius π raw v.maxBits size extent age budget small state)
  let active:=(v.wide_funded_stock_at_size h width v.radius π raw v.maxBits size extent age budget small).mounted_all
  let word:=(v.wide_stock_sizes h width ((le_max_right ..).trans age) budget small).words.addresses
  let pageRoom:=(v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width)
    ((le_max_left ..).trans age) budget).1
  let values:=Classical.choose_spec (Filter.eventually_atTop.1 v.wide_wire_paid) h
    ((le_max_left _ _).trans ((le_max_right _ _).trans height)) width small budget size enough π tape v.maxBits
  let ends:=Classical.choose_spec (Filter.eventually_atTop.1 v.wire_paid_ends) h
    ((le_max_right _ _).trans ((le_max_right _ _).trans height)) width small budget size enough π tape v.maxBits
  let _receipt := paid.1
  let mid := v.wideSignedMidAt h width size stock v.radius π order tape
  let _generic := @dated_wire_of_run.{0} F _ k p q Q σ Λ v h width v.maxBits π mid active word pageRoom
    (small.trans_lt (v.date_prefix_fit h))
  let _commodityFintype : Fintype (Commodity (Fin (2^h)) (Stages h (2^v.W)) k) := inferInstance
  (withDatedReceipt _generic _commodityFintype _receipt) values.1 ends

/-- The indexed counterpart of `wide_dated_wire` on the same completion
and the same reserve receipts. Each original edge remains distinguishable. -/
abbrev wide_dated_amounts (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
    (extent : v.wideFundedSize h width v.maxBits≤ size) (height : v.wideDatedLedgerHeight≤h)
    (small : width≤2^h) (budget : v.keepLimit*width+1≤2^h) (state : Word w) :=
  let tape:=v.wideFundedRaw h width v.maxBits raw
  let enough:= (v.wide_funded_extent h width v.maxBits).trans extent
  let age:= (le_max_left _ _).trans height
  let paid:=Classical.choose_spec (v.wide_funded_run_at h width v.radius π raw v.maxBits size extent age budget small state)
  let active:=(v.wide_funded_stock_at_size h width v.radius π raw v.maxBits size extent age budget small).mounted_all
  let word:=(v.wide_stock_sizes h width ((le_max_right ..).trans age) budget small).words.addresses
  let pageRoom:=(v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width)
    ((le_max_left ..).trans age) budget).1
  let values:=Classical.choose_spec (Filter.eventually_atTop.1 v.wide_wire_paid) h
    ((le_max_left _ _).trans ((le_max_right _ _).trans height)) width small budget size enough π tape v.maxBits
  let _receipt := paid.1
  let mid := v.wideSignedMidAt h width size stock v.radius π order tape
  let _generic := @dated_amounts_of_run.{0} F _ k p q Q σ Λ v h width v.maxBits mid active word pageRoom
    (small.trans_lt (v.date_prefix_fit h))
  let _commodityFintype : Fintype (Commodity (Fin (2^h)) (Stages h (2^v.W)) k) := inferInstance
  (withDatedReceipt _generic _commodityFintype _receipt) values.1

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

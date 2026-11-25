import OAI.Hierarchy.TaggedWideFinalDatedValue
import OAI.Hierarchy.TaggedWideNumberedBranchRoles

namespace OAI
/-! # Amounts in the physical chronological role order at the final boundary -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 550000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph
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


variable (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "bits" => v.maxBits
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
open private reportCost reportDates reportEntries reportSites from
  OAI.Hierarchy.TaggedWideNumberedBranchRoles

variable (horizon : v.wideFundedSize h width v.maxBits ≤ size) (age : v.wideFundedHeight ≤ h)
    (budget : v.keepLimit * width + 1 ≤ 2^h) (small : width ≤ 2^h)
    (cost : reportCost v h width size π raw)
local notation "days" => v.birthMarks P h width r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows) mid
variable {dates : reportDates v h width size π raw} {pos : 0 < Fintype.card (Columns h (2^v.W)) * k}
local notation "issues" => reportEntries v h width size π raw dates

local notation "who" => reportSites v h width size π raw dates pos
local notation "dur" => CatalystArchive.debit (count := num) (payload := width) v.mesh issues
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))

local notation "cardFit" => v.wide_dated_bought_rows h width
local notation "names" => timeRows v.sampler π v.depth days (P).catalogue order cardFit pair
local notation "emb" => DatedRows.embed v.sampler π v.depth days (P).catalogue order cardFit
local notation "catalog" => (P).catalogue.ordinal v.sampler π v.depth days order cardFit
local notation "whereAt" => HistoryRoles.sorted v.sampler π v.depth days
local notation "V" => v.wideDatedValue h width bits mid chk issues

open WireTelescope.CalendarTape
local notation "es" => events v.mesh
local notation "physicalCap" c:arg => HistoryRoles.ceiling v.sampler (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh c v.keepLimit (fuel v.mesh) width
local notation "excl" => v.paid_days_exclusive h width r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows) mid

variable {X : Type} {slot : Event → CalendarTape.Slot X} {initial : X} (unitCost : ℕ)
    (j : CalendarTape.Path slot (events v.mesh) initial)
    (wire : CalendarTape.Prefix.Cursor slot (events v.mesh) initial → Widths (siteLast h (2^v.W) k + 1))
private abbrev AmountRow := Sigma fun n : ℕ => Fin n → ℕ
private def getRoleRow {Y : Type} {sl : Event → CalendarTape.Slot Y} {events_ : List Event} {base : Y}
    {height wordWidth dim jobs : ℕ} {sampler : PurchaseSampler} {perm : Equiv.Perm (Fin (2^height))}
    {depth : ℕ} {cap : Public sampler height wordWidth dim jobs → ℕ}
    {wired : CalendarTape.Prefix.Cursor sl events_ base → Widths (siteLast height (2^wordWidth) dim + 1)}
    {path : CalendarTape.Path sl events_ base} (R_ : BranchRoles sampler perm depth cap wired path)
    (i : Fin (events_.length + 1)) : AmountRow := ⟨R_.count, R_.bits i⟩

private theorem transportedAmount {lhs rhs : AmountRow} (same : lhs = rhs) :
    lhs.2 = fun i => rhs.2 (Fin.cast (congrArg Sigma.fst same) i) := by
  cases same
  rfl

private theorem getRoleAmount {Y : Type} {sl : Event → CalendarTape.Slot Y} {events_ : List Event} {base : Y}
    {height wordWidth dim jobs : ℕ} {sampler : PurchaseSampler} {perm : Equiv.Perm (Fin (2^height))}
    {depth : ℕ} {cap : Public sampler height wordWidth dim jobs → ℕ}
    {wired : CalendarTape.Prefix.Cursor sl events_ base → Widths (siteLast height (2^wordWidth) dim + 1)}
    {path : CalendarTape.Path sl events_ base} (R_ : BranchRoles sampler perm depth cap wired path)
    (i : Fin (events_.length + 1))
    {rowCountBound : ℕ} (values : Fin rowCountBound → ℕ) (countEq : R_.count = rowCountBound)
    (same : getRoleRow R_ i = (⟨rowCountBound, values⟩ : AmountRow)) :
    R_.bits i = fun a => values (Fin.cast countEq a) :=
  transportedAmount same

private theorem paidOrdinaryAt {sourceType : Type} (dated_ final_ : sourceType → ℕ)
    (physicalValue : ℕ) (account_ : sourceType) (identified : physicalValue = dated_ account_)
    (lastValue : dated_ = final_) : physicalValue = final_ account_ :=
  identified.trans (congrFun lastValue account_)

include horizon age budget small cost

private theorem rolePair_at
    (receipt : Whole.Reconciliation (n := recordCount (count := num) (payload := width) v.mesh issues) (count := num) («w» := w) sink original supply who dur ord ci pair archive)
    (funded : v.WideFundedAlignment h width size bits π raw who dur (fun j=>(pair j).val))
    (bounded : v.DatedWireFits h width π mid chk unitCost)
    (atTime : ∀i:Fin ((es).length+1),v.wideDatedWire h width bits π mid chk issues i.val=wire (Prefix.boundaryIndex j i)) :
    letI : Nonempty (Fin k) := ⟨⟨0, v.positive⟩⟩
    getRoleRow ((v.numberedBranchRoles h width size π raw horizon age budget small cost unitCost j wire
      (dates:=dates) (pos:=pos) receipt funded bounded atTime)) (Fin.last (es).length) = ⟨Fintype.card (Source v.sampler π v.depth days),
      V (es).length ∘ emb ∘ names⟩ := by
  rfl

section
attribute [local irreducible] numberedBranchRoles

private abbrev datedRoleConclusion
    (receipt : Whole.Reconciliation (n := recordCount (count := num) (payload := width) v.mesh issues) (count := num) («w» := w) sink original supply who dur ord ci pair archive)
    (funded : v.WideFundedAlignment h width size bits π raw who dur (fun j=>(pair j).val))
    (bounded : v.DatedWireFits h width π mid chk unitCost)
    (atTime : ∀i:Fin ((es).length+1),v.wideDatedWire h width bits π mid chk issues i.val=wire (Prefix.boundaryIndex j i)) : Prop :=
    letI : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
    let picked := v.numberedBranchRoles h width size π raw horizon age budget small cost unitCost j wire
      (dates:=dates) (pos:=pos) receipt funded bounded atTime
    let packed := rolePair_at v h width size π raw horizon age budget small cost unitCost j wire
      (dates:=dates) (pos:=pos) receipt funded bounded atTime
    let cardinality : picked.count = Fintype.card (Source v.sampler π v.depth days) := congrArg Sigma.fst packed
    picked.bits (Fin.last (es).length) =
      fun i : Fin picked.count => V (es).length (emb (names (Fin.cast cardinality i)))

open Lean Elab Tactic in
private theorem datedRoleAmounts
    (receipt : Whole.Reconciliation (n := recordCount (count := num) (payload := width) v.mesh issues) (count := num) («w» := w) sink original supply who dur ord ci pair archive)
    (funded : v.WideFundedAlignment h width size bits π raw who dur (fun j=>(pair j).val))
    (bounded : v.DatedWireFits h width π mid chk unitCost)
    (atTime : ∀i:Fin ((es).length+1),v.wideDatedWire h width bits π mid chk issues i.val=wire (Prefix.boundaryIndex j i)) :
    datedRoleConclusion v h width size π raw horizon age budget small cost unitCost j wire
      (dates:=dates) (pos:=pos) receipt funded bounded atTime := by
  unfold datedRoleConclusion
  intro picked packed cardinality
  run_tac withMainContext do
    let observed ← Meta.getFVarFromUserName `packed
    let countEq ← Meta.getFVarFromUserName `cardinality
    let eqn ← Meta.whnf (← Meta.inferType observed)
    let role_ := eqn.getAppArgs[1]!
    let value_ := eqn.getAppArgs[2]!
    unless role_.getAppFn.isConstOf ``getRoleRow && value_.getAppFn.isConstOf ``Sigma.mk do
      throwError "expected the selected numbered row"
    let proof := mkAppN (mkConst ``getRoleAmount)
      (role_.getAppArgs ++ #[value_.getAppArgs[2]!,value_.getAppArgs[3]!,countEq,observed])
    (← getMainGoal).assign proof
    replaceMainGoal []
end

private abbrev ordinaryRoleConclusion
    (state : Word w)
    (align : ∀{n : ℕ}(owner : Fin n→Fin num)(fees : Fin n→ℕ),
      v.WideFundedAlignment h width size bits π raw owner fees (fun z=>(pair z).val))
    (receipt : Whole.Reconciliation (n := recordCount (count := num) (payload := width) v.mesh issues) (count := num) («w» := w) sink original supply who dur ord ci pair archive)
    (funded : v.WideFundedAlignment h width size bits π raw who dur (fun j=>(pair j).val))
    (bounded : v.DatedWireFits h width π mid chk unitCost)
    (atTime : ∀i:Fin ((es).length+1),v.wideDatedWire h width bits π mid chk issues i.val=wire (Prefix.boundaryIndex j i)) : Prop :=
    letI : Nonempty (Fin k) := ⟨⟨0, v.positive⟩⟩
    let Z:=v.wide_native_report h width size π raw bits horizon age budget small cost state align
    (v.numberedBranchRoles h width size π raw horizon age budget small cost unitCost j wire (dates:=dates) (pos:=pos) receipt
      funded bounded atTime).bits (Fin.last (es).length)=
      SettledMatrix.Layout.available Z.fixed Z.stock Z.reserved Z.used ∘ emb ∘ names


open Lean Elab Tactic in
theorem numbered_final_amounts
    (state : Word w)
    (align : ∀{n : ℕ}(owner : Fin n→Fin num)(fees : Fin n→ℕ),
      v.WideFundedAlignment h width size bits π raw owner fees (fun z=>(pair z).val))
    (receipt : Whole.Reconciliation (n := recordCount (count := num) (payload := width) v.mesh issues) (count := num) («w» := w) sink original supply who dur ord ci pair archive)
    (funded : v.WideFundedAlignment h width size bits π raw who dur (fun j=>(pair j).val))
    (bounded : v.DatedWireFits h width π mid chk unitCost)
    (atTime : ∀i:Fin ((es).length+1),v.wideDatedWire h width bits π mid chk issues i.val=wire (Prefix.boundaryIndex j i)) :
    ordinaryRoleConclusion v h width size π raw horizon age budget small cost unitCost j wire state align
      (dates:=dates) (pos:=pos) receipt funded bounded atTime := by
  unfold ordinaryRoleConclusion
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  have reading := datedRoleAmounts v h width size π raw horizon age budget small cost unitCost j wire
    (dates:=dates) (pos:=pos) receipt funded bounded atTime
  have plainReading := v.wide_final_dated_value h width size π raw bits horizon age budget small cost state align dates
  funext i
  have atRole := congrFun reading i
  run_tac withMainContext do
    let marked ← Meta.getFVarFromUserName `atRole
    let ordinary ← Meta.getFVarFromUserName `plainReading
    let observed ← Meta.whnf (← Meta.inferType marked)
    let regularEq ← Meta.whnf (← Meta.inferType ordinary)
    let application := observed.getAppArgs[2]!.headBeta
    let account_ := application.getAppArgs.back!
    let original_ := regularEq.getAppArgs[1]!
    let sourceType := (← Meta.whnf (← Meta.inferType original_)).bindingDomain!
    let proof := mkAppN (mkConst ``paidOrdinaryAt) #[sourceType,original_,regularEq.getAppArgs[2]!,
      observed.getAppArgs[1]!,account_,marked,ordinary]
    (← getMainGoal).assign proof
    replaceMainGoal []

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

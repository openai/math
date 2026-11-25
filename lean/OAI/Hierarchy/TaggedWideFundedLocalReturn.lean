import OAI.Hierarchy.ProbeFixedWideSpillAccessSource
import OAI.Hierarchy.TaggedWideFundedProcessing
import OAI.Hierarchy.TaggedWideReturnSpillRoom
import OAI.Hierarchy.TaggedWideFundedTurnArchive
import OAI.Hierarchy.ProbeFixedWideCorrectedSpillRun
import OAI.Hierarchy.TaggedWideFundedCountedReads
import OAI.Hierarchy.TaggedWideFundedPortWords
import OAI.Hierarchy.TaggedWideFundedROM

namespace OAI
/-! # Funded cut readouts on the actual dated and terminal machine -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open scoped Classical BigOperators Fin.CommRing
open Tagged Tagged.WideStack
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ B : ℝ} (x : WideParent κ B)
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 36000000
set_option cleanup.letToHave false
local notation "h" => x.h
local notation "width" => x.w
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
local notation "order" => v.wideOrder h width

local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
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
local notation "o" => wideRouteOrder h D k

open TaggedShorterBudget TaggedShorterSupergroups ProtocolRAMReportedPorts
open Computability.VPVNP.RAMMemory
open CalendarTape
/-- The electrical observations returned by the original spill scan, indexed by
its actual input and output memories. -/
def SpillFields {W first ticks : ℕ} {p : Procedure W} {initial : Memory W}
    {fields : Memory W → Prop}
    (_ : ∃out,p.Exec initial out ticks ∧ (∀a, a < first → out a=initial a) ∧ fields out) :
    Memory W → Prop := fields

/-- The type determined by the actual paid source chosen inside the run. -/
abbrev SpillDataType {α : Sort*} (_ : α) := α

variable (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
local notation "bits" => v.maxBits
local notation "ss" => v.widePaidSlices h width bits
local notation "es" => events v.mesh
local notation "dated" => v.wideDated h width ell unitCost
local notation "root" => v.wideInstalledRoot x
local notation "size" => v.wideInstalledSize x m ell unitCost dated
local notation "issuedSize" => (dated).romEnd root
local notation "fieldsEnd" => (dated).workEnd size
local notation "l" => v.wideInstalledLayout x m ell short u δ ξ unitCost dated
local notation "full" => v.wideFundedSize h width bits
local notation "dest" => TerminalLayout.destination page
local notation "locked" => (v.wideWidthLayout h width ss).bank (es).length
local notation "geo" => typeMenu κ B v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)
local notation "menu" => (geo).menu u δ ξ
local notation "slots" => purchaseSlots h v.W k v.wideJobs ell
local notation "U" => (l).pruneScratch+(l).pruneRows+1
local notation "advice" => v.wideInstalledHeader x m ell short u δ ξ unitCost dated rfl rfl
variable (highRaw : Memory w) (age : v.wideStockHeight ≤ h) (budget : v.keepLimit*width+1 ≤ 2^h)
    (small : width ≤ 2^h) (ready : CountedReady v h width bits)
local notation "reader" => v.wideSelector h width age budget small
local notation "head0" => advice highRaw
local notation "sl" => (reader).format.slot
local notation "windows" => (reader).format.windows
variable {E : Type} (label : Tagged.Row h×Fin h→E) (e : E→Bool)
    (word : Bits (CalendarTape.bits sl es)) (external : Equiv.Perm (Fin (2^h)))
    (auth : ∀i,WordSlots.exposed label e i=external i)
local notation "pi0" => external.symm
local notation "input" => (windows).header es word head0
local notation "tagged" => (windows).tape es label (v.wideFixedCPUInput h width size head0) e word
local notation "seed" => v.wideFundedRaw h width bits input
local notation "mid" => v.wideSignedMidAt h width size stock v.radius pi0 o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock v.radius pi0 o seed
local notation "initialOrigin" => v.wideSignedMidAt h width size stock v.radius pi0 o (v.wideFundedRaw h width bits head0)
local notation "days" => v.birthMarks P h width r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows) mid
variable (found : ∃! j : Path sl es initialOrigin,encode sl es initialOrigin j=word)
    (lim : v.FullGateRoom x m ell short u δ ξ unitCost)
    (registers : size+2*(2^h) < 2^w) (operandAge : v.wideOperandHeight ≤ h)
    (activeAge : v.wideDatedSupportHeight ≤ h) (ballotAge : v.wideBallotHeight ≤ h)
    (large : purchaseWordHeight v.W k v.wideJobs ell ≤ h)
    (lanesFit : v.wideInstalledCap unitCost ≤ 2^ell)
    (cost : ∀i : Fin rows,PaidWidths.total ss chk i+(v.overflowFactor v.keepLimit+fuel v.mesh)*width < 2^w)
    (names : ∀{n : ℕ}(owner : Fin n→Fin num)(debits : Fin n→ℕ),
      v.WideFundedAlignment h width size bits pi0 input owner debits (fun j=>(pairKeys (Columns h D) k j).val))
local notation "bounds" => v.wide_installed_tape_bounds x m ell unitCost dated
local notation "native" => v.wide_native_report h width size pi0 input bits (bounds).2.2 ready.height
  ready.credit ready.size_le cost 0 names
variable (actual : v.FundedCutRows h width size pi0 input (native).rows (native).geometry unitCost)
    (prices : v.PhysicalCounts u B δ ξ m) {C₀ : ℝ} (pricePos : 0 ≤ κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates h v.W k v.wideJobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C₀)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x ≤ (menu).payload t x)
    (quote : v.PrunePrices h width (native).rows)
    (spillRoom : v.ReturnSpillRoom x m ell short u δ ξ unitCost)
    (spillAge : v.wideSpillSheetHeight ≤ h) (paidAge : v.wideSpillPaidHeight ≤ h)
    (spillBallotAge : v.wideSpillBallotHeight ≤ h) (widthFloor : v.widthFloor ≤ width)

attribute [local irreducible] ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec
  CatalystArchive.recordCount CatalystArchive.issued
  CatalystArchive.nativeSite CatalystArchive.debit

/- Recover the dates from the reconciliation's actual count of issued records. -/
open Lean Elab Term in
local elab "localReportDates " cert:ident : term => do
  let receipt ← Meta.getFVarFromUserName cert.getId
  let reconciliation ← Meta.whnf (← Meta.inferType receipt)
  unless reconciliation.getAppFn.isConstOf ``Whole.Reconciliation do
    throwError "expected a settlement reconciliation"
  let some rowCountExpr := reconciliation.getAppArgs[7]? | throwError "expected a reconciliation record count"
  let count ← Meta.whnf rowCountExpr
  unless count.getAppFn.isConstOf ``CatalystArchive.recordCount do
    throwError "expected the native record count"
  let issuedExpr ← Meta.whnf count.getAppArgs.back!
  unless issuedExpr.getAppFn.isConstOf ``CatalystArchive.issued do
    throwError "expected the dated issues"
  return ← instantiateMVars issuedExpr.getAppArgs.back!

/- All operands have already been recovered from the same execution. Construct the
application directly so elaboration does not expand the complete stored memories for each operand. -/
open Lean Elab Term in
local elab "applyStoredExecution " fn:ident " using " args:term,+ : term => do
  let procedure ← Meta.getFVarFromUserName fn.getId
  let operands ← args.getElems.mapM fun arg => elabTerm arg none
  return mkAppN procedure operands

open Lean Elab Term in
local elab "localPageMemory " proof:ident : term => do
  let fact ← Meta.getFVarFromUserName proof.getId
  let ty ← Meta.whnf (← Meta.inferType fact)
  unless ty.getAppFn.isConstOf ``WideDatedPages do
    throwError "expected the physical date pages"
  return ← instantiateMVars ty.getAppArgs[ty.getAppArgs.size - 2]!

open Lean Elab Term in
local elab "localEmittedInput " proof:ident : term => do
  let fact ← Meta.getFVarFromUserName proof.getId
  Meta.forallTelescopeReducing (← Meta.inferType fact) fun _ prop => do
    unless prop.isAppOf ``Eq do throwError "expected the report-word equality"
    let word := prop.getAppArgs.back!
    unless word.getAppFn.isConstOf ``ProtocolRAMEmit.emitted do
      throwError "expected the emitted report memory"
    return ← instantiateMVars word.getAppArgs[word.getAppArgs.size - 2]!

private theorem issuedFitsWork {issuedLength work : ℕ} (gap : 3 * issuedLength + 2 ≤ work) : issuedLength ≤ work := by
  omega

/-- At the constant stage, the stored word is the width of the selected row. -/
private theorem storedScaleWidth {count wordSize : ℕ} (positive : Fin count → Prop)
    (row : Fin count → ProtocolRAMEmit.Row) (i : Fin count) (value : Word wordSize)
    (stored : value = ((if decide (positive i) then (row i).width else 0 : ℕ) : Word wordSize)) :
    value = ((atScale positive (fun _ => 0) 0 row i).width : Word wordSize) := by
  simpa only [atScale, eq_self, and_true, decide_eq_true_eq] using stored

private theorem attachWindowReceipt {α : Type} {post ran flag low cells receipt : α → Prop}
    (execution : ∃ out, post out ∧ ran out ∧ flag out ∧ low out ∧ cells out)
    (package : ∀ out, cells out → receipt out) :
    ∃ out, post out ∧ ran out ∧ flag out ∧ low out ∧ receipt out := by
  obtain ⟨out, observed, executed, pruned, retained, printed⟩ := execution
  exact ⟨out, observed, executed, pruned, retained, package out printed⟩

private theorem attachSpillObservation {α : Type} {ran frame fields observation : α → Prop}
    (execution : ∃ out, ran out ∧ frame out ∧ fields out)
    (package : ∀ out, fields out → observation out) :
    ∃ out, ran out ∧ frame out ∧ observation out := by
  obtain ⟨out, executed, retained, readouts⟩ := execution
  exact ⟨out, executed, retained, package out readouts⟩

/- Apply the two existential mapping lemmas directly to the predicates recorded in
the actual run. This avoids reducing the entire program to infer the eliminator motive. -/
open Lean Elab Term in
private def extendExecutedOutput (lemmaName : Name) (preserved : Nat) (final pack : Syntax) :
    TermElabM Lean.Expr := do
  let execution ← Meta.getFVarFromUserName final.getId
  let package ← Meta.getFVarFromUserName pack.getId
  let existsType ← Meta.whnf (← Meta.inferType execution)
  unless existsType.isAppOf ``Exists do throwError "expected an executed output witness"
  let memory := existsType.getAppArgs[0]!
  Meta.withLocalDeclD `out memory fun out => do
    let mut facts := #[]
    let mut current := (mkApp existsType.getAppArgs[1]! out).headBeta
    for _ in [:preserved] do
      current ← Meta.whnf current
      unless current.isAppOf ``And do throwError "expected the executed output observations"
      facts := facts.push (← Meta.mkLambdaFVars #[out] current.getAppArgs[0]!)
      current := current.getAppArgs[1]!
    facts := facts.push (← Meta.mkLambdaFVars #[out] current)
    let packing ← Meta.whnf (← Meta.inferType (mkApp package out))
    unless packing.isForall && !packing.bindingBody!.hasLooseBVar 0 do
      throwError "expected an observation at the same output memory"
    let receipt ← Meta.mkLambdaFVars #[out] packing.bindingBody!
    return mkAppN (mkConst lemmaName) (#[memory] ++ facts ++ #[receipt, execution, package])

open Lean Elab Term in
local elab "attachExecutedWindow " final:ident " using " pack:ident : term =>
  extendExecutedOutput ``attachWindowReceipt 4 final pack

open Lean Elab Term in
local elab "attachExecutedSpill " final:ident " using " pack:ident : term =>
  extendExecutedOutput ``attachSpillObservation 2 final pack

/- Preserve the inferred propositions of all three observations when pairing them. -/
open Lean Elab Term in
local elab "joinLocalReturn " counted:ident published:ident complete:ident : term => do
  let countedRun ← Meta.getFVarFromUserName counted.getId
  let localRun ← Meta.getFVarFromUserName published.getId
  let observedRun ← Meta.getFVarFromUserName complete.getId
  let localProp ← Meta.inferType localRun
  let observedProp ← Meta.inferType observedRun
  let pair := mkAppN (Lean.mkConst ``And.intro) #[localProp, observedProp, localRun, observedRun]
  return mkAppN (Lean.mkConst ``And.intro)
    #[← Meta.inferType countedRun, mkApp2 (Lean.mkConst ``And) localProp observedProp, countedRun, pair]

/- Infer the result after closing the dependent local execution, so no output
type metavariable is shared across the binders for its intermediate memories. -/
open Lean Elab Term in
local elab "inferExecutedReturn% " body:term : term => elabTerm body none

/-- Compile from the actual funded calendar and its retained per-event directories.
The final continuation receives the same terminal output that feeds all windows:
its role fields and the two paid socket sides come from a single chronological execution. -/
abbrev wide_funded_local_return := inferExecutedReturn%
  let limits:=v.wide_funded_local_room x m ell short u δ ξ unitCost lim
  let sites:=v.wide_dated_sites h width ell unitCost
  let edges:=v.wide_dated_edges h width ell unitCost
  let pre:=v.wideTerminalPreimage x dated sites edges highRaw
  let windowInput:=v.wideTerminalWords h width bits issuedSize fieldsEnd pre
  let accepted:=(v.wide_funded_admission h width age budget small bits size
    ((v.wide_funded_extent h width bits).trans (bounds).2.2) v.radius pi0 head0 word).2 found
  let counted:=v.wide_counted_local_reads h width size pi0 input (bounds).2.2 ready accepted
  let cut:=counted.2
  let paid:=cut.2.2.2
  let receipt:=paid.2.1
  let certificate := cut.1
  let pageReads := cut.2.2.1
  let archiveState := localPageMemory pageReads
  let reportFrame := receipt.1
  let reportInput := localEmittedInput reportFrame
  let reportDates : Dates C mid L pay num width := localReportDates certificate
  let issues := CatalystArchive.issued (chart := C) (initial := mid) («L» := L) (base := pay)
    (count := num) (payload := width) reportDates
  have accounts : 0 < num := Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨.inl ⟨0,Nat.two_pow_pos _⟩⟩) v.positive
  let owner := CatalystArchive.nativeSite (count := num) (payload := width) («w» := w) L v.mesh issues accounts chk
  let debits := CatalystArchive.debit (count := num) (payload := width) v.mesh issues
  have issueCount : recordCount v.mesh issues = cnt := recordCount_rowOnly v.mesh issues decl (issued_rows reportDates)
  let alignment := names owner debits
  letI : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  have exclusive : Exclusive days := by apply v.paid_days_exclusive
  let header:=v.wide_inverse_installed_rom x m ell short u δ ξ unitCost dated sites edges highRaw
    age budget small label ready registers e word external auth found
  let inv:=v.wide_tag_inverse_entry h width age budget small size head0 label
    ((v.wide_funded_extent h width bits).trans (bounds).2.2)
    ((bounds).1.trans ((bounds).2.1.trans (bounds).2.2)) registers e word external auth
  let source:=v.wide_funded_issuer_rom x m ell short u δ ξ unitCost dated sites edges highRaw _ header.2
  let localProgram := v.wide_local_run h width size v.radius pi0 input (bounds).2.2 ready.height ready.credit
    ready.size_le operandAge issues issueCount owner days exclusive alignment.1.some ell unitCost root size archiveState pre
  let locals := applyStoredExecution localProgram using pageReads, certificate, cut.2.1.1, alignment.2,
    paid.1, receipt.2.2, cost, limits.highFit, activeAge, ballotAge, (rfl : v.radius = v.radius),
    limits.afterReplay, limits.top, limits.funded, limits.gap, limits.publicRoom, limits.room, highRaw,
    reportInput, reportFrame, limits.beforeROM, receipt.2.1, source.1, source.2
  let after:=Classical.choose locals
  let before:=Classical.choose (Classical.choose_spec locals)
  let published:=Classical.choose_spec (Classical.choose_spec locals)
  let keptROM:=v.wide_funded_local_rom x m ell short u δ ξ unitCost dated sites edges highRaw _ before header.2
    published.2.1
  let endpoints:=FundedCutRows.port_words v x size pi0 input (bounds).2.2 ready.height ready.credit
    ready.size_le ell unitCost (dates := reportDates) (pos := accounts) (native).geometry actual operandAge limits.highFit _ paid.1 m short u δ ξ before
    published.2.2.2.2.2.1
  let stored (t : Fin (m+1)) (j : Fin rows) :
      ((l).inputs t).width.read before ((3*j.val:ℕ):Word w)=
      ((atScale ((P).catalogue.transport order) (fun _=>0) 0 (native).rows j).width:Word w) := by
    exact storedScaleWidth ((P).catalogue.transport order) (native).rows j _ (published.2.2.2.2.1 j)
  let returnPaid (Post : Memory w→Prop) := fun spill =>
    FundedCutRows.full_program_with v x size pi0 input m ell short unitCost (native).rows (native).geometry actual
      prices pricePos buy groupsFit metadata lanesFit lim large windowInput before _ keptROM.1
      published.2.2.1 endpoints keptROM.2.1 quote keptROM.2.2 stored Post tagged _ _ inv
      counted.1 published.1 spill
  let lastFields:=published.2.2.2.2.2.2.2.2.2
  have baseFloor : size ≤ (l).floor := v.wide_installed_size_le_field_floor x m ell short u δ ξ unitCost dated
  have heapSize : (v.wideReserveLayout h width ss).scratch ≤ size :=
    (Nat.le_add_right ..).trans limits.afterReplay
  have sizeWord : size < 2^w := (Nat.le_add_right ..).trans_lt registers
  let captured (atPrune : Memory w) (prior : ∀a, a < (l).floor → atPrune a=before a) :
      ProcessingArchive ((A).endAddress v.mesh) root issuedSize chk pre atPrune := by
    let earlier (a) (ha : a < size) := (prior a (ha.trans_le baseFloor)).trans (published.2.1 a ha)
    refine ⟨?_,?_⟩
    · exact fun a ha=>
        (earlier a (ha.trans_le ((v.wide_funded_extent h width bits).trans limits.funded))).trans (receipt.2.1 a ha)
    · exact fun a lo hi=>(earlier a (hi.trans_le (issuedFitsWork limits.gap))).trans
        (source.1 a lo hi)
  let turnAt (atPrune : Memory w) (prior : ∀a, a < (l).floor → atPrune a=before a) :=
    v.wide_turn_source_from_local h width size v.radius pi0 input issues owner (pairKeys (Columns h D) k)
      days exclusive alignment.1.some ell unitCost root size _ pre after before
      paid.1 limits.funded limits.publicRoom limits.room source.2 published.2.1
      lastFields.1 lastFields.2.2.1 lastFields.2.2.2 atPrune prior
  let perform (atPrune : Memory w) (prior : ∀a, a < (l).floor → atPrune a=before a) :=
    let earlier (a) (ha : a < size) := (prior a (ha.trans_le baseFloor)).trans (published.2.1 a ha)
    let same (a) (ha : a < full) := (earlier a (ha.trans_le limits.funded)).trans (paid.1 a ha)
    let livePages:=cut.2.2.1.frame size heapSize sizeWord earlier
    let dir:=v.wide_counted_directory h width size pi0 input (dates := reportDates) (pos := accounts) atPrune certificate same
    let preserved:=captured atPrune prior
    let turns:=turnAt atPrune prior
    let spillProgram := v.wide_corrected_spill_run h width size v.radius pi0 input (bounds).2.2 ready.height ready.credit
      ready.size_le operandAge issues issueCount owner (pairKeys (Columns h D) k) days
      exclusive alignment.1.some ell unitCost U root size issuedSize fieldsEnd atPrune
    applyStoredExecution spillProgram using livePages, certificate, same, cost, limits.highFit, spillAge,
      (rfl : v.radius = v.radius), widthFloor, accepted, dir, spillRoom.archiveFloor,
      spillRoom.headFloor, spillRoom.funded, spillRoom.heap, paidAge, spillBallotAge, preserved.checkout, spillRoom.top,
      (fun j : Fin rows => decide ((P).catalogue.transport order j)), highRaw, preserved.rom, spillRoom.gap,
      spillRoom.oldBefore, spillRoom.room, spillRoom.wide, spillRoom.endRoom, turns, alignment.2,
      spillRoom.readOnly, spillRoom.replayed, spillRoom.terminalFloor
  let registersAt (atPrune : Memory w) (prior : ∀a, a < (l).floor → atPrune a=before a)
      (out : Memory w) (fields : SpillFields (perform atPrune prior) out) :=
    let ranked:=fields.choose
    let sch:=fields.choose_spec.choose
    let inputs:=fields.choose_spec.choose_spec.choose
    let origin:=fields.choose_spec.choose_spec.choose_spec.choose
    let result:=fields.choose_spec.choose_spec.choose_spec.choose_spec
    let same (i) (hi : i<full) :=
      (prior i (hi.trans_le (limits.funded.trans baseFloor))).trans
        ((published.2.1 i (hi.trans_le limits.funded)).trans (paid.1 i hi))
    (show v.NativeSpillRegisters h width size v.radius pi0 input (bounds).2.2 ready.height ready.credit
      ready.size_le operandAge issues issueCount owner (pairKeys (Columns h D) k) days
      exclusive alignment.1.some ell unitCost U root size issuedSize fieldsEnd
      atPrune ranked sch out inputs from
      ⟨turnAt atPrune prior,origin,cut.1,alignment.2,cost,rfl,paidAge,(captured atPrune prior).checkout,same,
        spillRoom.readOnly,spillRoom.replayed,spillRoom.terminalFloor,spillRoom.funded,spillRoom.oldBefore,
        spillRoom.gap,spillRoom.room,result.1,result.2.1,result.2.2.1,result.2.2.2.2.1,
        result.2.2.2.2.2.1,result.2.2.2.2.2.2⟩)
  let observed (out : Memory w) := ∃(atPrune : Memory w) (low : ∀a, a < (l).floor → atPrune a=before a),
    SpillFields (perform atPrune low) out ∧
      ProcessingArchive ((A).endAddress v.mesh) root issuedSize chk pre atPrune ∧
      (∀ fields : SpillFields (perform atPrune low) out, Nonempty (SpillDataType (registersAt atPrune low out fields)))
  let spillObserved (atPrune : Memory w) (low : ∀a, a < (l).floor → atPrune a=before a) :=
    let executed := perform atPrune low
    let attach (out : Memory w) (readouts : SpillFields executed out) : observed out :=
      ⟨atPrune, low, readouts, captured atPrune low, fun reading => ⟨registersAt atPrune low out reading⟩⟩
    attachExecutedSpill executed using attach
  let final := applyStoredExecution returnPaid using observed, spillObserved
  let package (out : Memory w) (cells : _) : FundedCutRows.WindowReceipt v x size pi0 input
      m ell short unitCost (native).rows (native).geometry actual prices pricePos buy groupsFit
      metadata lanesFit lim large windowInput before _ out :=
    ⟨keptROM.1,published.2.2.1,endpoints,cells⟩
  let complete := attachExecutedWindow final using package
  let countedRun := counted.1
  joinLocalReturn countedRun published complete

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_funded_local_return"

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

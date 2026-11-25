import OAI.Hierarchy.TaggedWireDatedLedger
import OAI.Hierarchy.ProtocolRAMCatalystWirePrefix
import OAI.Hierarchy.ProbeCatalystPrefixKeys
import OAI.Hierarchy.ProbeFixedCatalystOwnerFits
import OAI.Hierarchy.ProbeFixedFundedWidth

namespace OAI
/-! # Reserve already withdrawn at the original signed calendar prefix -/
noncomputable section
set_option quotPrecheck false
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

private theorem debit_room (a : Attempt) (i : Fin ((L).rows (.attempt a))) :
    base (.attempt a)+i.val < (A).base v.mesh (.attempt a)+(A).stride := by
  let ar:=(fs a).pricedArea
  have hi : i.val < ar.occurrences := by
    have hn:=i.isLt
    cases a <;> exact hn
  refine lt_of_lt_of_le ?_ (v.attempt_room P h width a)
  change ar.direct+ar.occurrences+i.val < ar.stop
  unfold StockCommit.Area.stop StockCommit.Area.output StockCommit.Area.excess StockCommit.Area.clip
    StockCommit.Area.src StockCommit.Area.broadcast
  omega

/-- When two arbitrary memories agree through a completed event's slab,
both the selected owner and archived debit agree on every incidence. -/
theorem withdrawal_low (left right : Memory w) (word : flag<2^w) (t : Fin (es).length)
    (same : PrefixAgreement.Low ((A).base v.mesh ((es).get t)+(A).stride) left right) (a : pairs) :
    v.wireWithdrawal h width ((es).get t) left a=v.wireWithdrawal h width ((es).get t) right a := by
  have ownerFit:=v.catalyst_owner_args h width (WideMemory.K h v.W) (directory).groups
    (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k) (P).joint (P).catalogue
    (v.wideSources h width).2 own (v.wideGeometryPrefix h width).2.2 word t
  let ev:=(es).get t
  have expression (u : Word w) :
      ((L).term ev).eval left u=((L).term ev).eval right u := by
    exact PrefixAgreement.expr _ left right ((A).base v.mesh ev) (PrefixAgreement.inputEnd_of_fits _ ownerFit)
      (fun x hx=> same x (hx.trans_le (Nat.le_add_right ..))) u
  change v.wireWithdrawal h width ev left a=v.wireWithdrawal h width ev right a
  cases eq : ev with
  | feed _ => rfl
  | attempt b =>
    simp only [wireWithdrawal]
    apply Finset.sum_congr rfl
    intro i _
    have owners:=expression (i.val:Word w)
    rw [eq] at owners
    have span : base (.attempt b)+i.val<(A).base v.mesh ev+(A).stride := by rw [eq];exact v.debit_room h width b i
    rw [owners,same _ span]

theorem past_reserve_agreement (left right : Memory w) (word : flag<2^w) (j : ℕ)
    (same : PrefixAgreement.Low ((A).first+j*(A).stride) left right) (a : pairs) :
    v.wireUsedAt h width j left a=v.wireUsedAt h width j right a := by
  unfold wireUsedAt
  apply congrArg List.sum
  apply List.map_congr_left
  intro ev early
  obtain ⟨n,hn,eq⟩:=List.mem_take_iff_getElem.mp early
  let t : Fin (es).length:=⟨n,hn.trans_le (min_le_right ..)⟩
  have earlier : n < j:=hn.trans_le (min_le_left ..)
  have order : position v.mesh ((es).get t)=n:=position_at v.mesh t.isLt
  have space:=Nat.mul_le_mul_right (A).stride (show n+1 ≤ j from earlier)
  rw [Nat.add_mul,one_mul] at space
  have low : PrefixAgreement.Low ((A).base v.mesh ((es).get t)+(A).stride) left right:=by
    intro x hx
    rw [Arena.base,order] at hx
    exact same x (by omega)
  exact eq ▸ v.withdrawal_low h width left right word t low a

/-- Both the owner read and the amount read at a retired date are preserved
at every later prefix. This includes an inner attempt whose owner uses its
original parent's tile shelf. -/
theorem wire_withdrawal_at_prefix (initial : Memory w) (runReady : Calendar.mounted C es initial)
    (word : flag<2^w) (t : Fin (es).length) (j : ℕ) (past : t.val < j) (range : j≤(es).length)
    (a : pairs) :
    v.wireWithdrawal h width ((es).get t) (StockBound.state C initial j) a =
      v.wireWithdrawal h width ((es).get t) (checkedOut C flag initial) a := by
  have floor (e : Event) (x : ℕ) (hx : x<(A).base v.mesh e) := (v.event_prefix P h width r old (TerminalLayout.source page)
    (TerminalLayout.table page) (TerminalLayout.destination page) (sinkBank start cnt r rows) e x hx).1
  have ownerFit := v.catalyst_owner_args h width (WideMemory.K h v.W) (directory).groups
    (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k) (P).joint (P).catalogue
    (v.wideSources h width).2 own (v.wideGeometryPrefix h width).2.2 word t
  let ev:=(es).get t
  have bound : (A).base v.mesh ev+(A).stride ≤ flag:=(A).within v.mesh ev ((es).get_mem t)
  have baseHigh : (A).base v.mesh ev ≤ flag:=(Nat.le_add_right ..).trans bound
  have expr := fun row=> prefix_expr C A initial flag runReady floor t j past range ((L).term ev) row ownerFit baseHigh
  have address (x : ℕ) (hx : x<(A).base v.mesh ev+(A).stride) :=
    prefix_word C A initial flag runReady floor t j past range x hx (ne_of_lt (hx.trans_le bound))
  change v.wireWithdrawal h width ev _ a=v.wireWithdrawal h width ev _ a
  cases here : ev with
  | feed _ => rfl
  | attempt b =>
    simp only [wireWithdrawal]
    apply Finset.sum_congr rfl
    intro i _
    have sameOwner:=expr (i.val:Word w)
    rw [here] at sameOwner
    have fit : base (.attempt b)+i.val<(A).base v.mesh ev+(A).stride := by
      rw [here]
      exact v.debit_room h width b i
    change ((L).term (.attempt b)).eval (StockBound.state C initial j) (i.val : Word w) =
      ((L).term (.attempt b)).eval (checkedOut C flag initial) (i.val : Word w) at sameOwner
    have cell : StockBound.state C initial j (base (.attempt b)+i.val) =
        checkedOut C flag initial (base (.attempt b)+i.val) := address _ fit
    rw [sameOwner,cell]

theorem wire_used_preserved (initial : Memory w) (runReady : Calendar.mounted C es initial) (word : flag<2^w)
    (j : ℕ) (range : j≤(es).length) (a : pairs) :
    v.wireUsedAt h width j (StockBound.state C initial j) a=v.wireUsedAt h width j (checkedOut C flag initial) a := by
  unfold wireUsedAt
  apply congrArg List.sum
  apply List.map_congr_left
  intro ev member
  obtain ⟨time,small,same⟩:=List.mem_take_iff_getElem.mp member
  let t : Fin (es).length:=⟨time,small.trans_le (min_le_right ..)⟩
  exact same ▸ v.wire_withdrawal_at_prefix h width initial runReady word t j (small.trans_le (min_le_left ..)) range a

/-- Only the debit for this event separates the two successive active memories. -/
theorem wire_used_retired_step (initial : Memory w) (runReady : Calendar.mounted C es initial)
    (word : flag<2^w) (t : Fin (es).length) (a : pairs) :
    let next:=StockBound.state C initial (t.val+1)
    v.wireUsedAt h width (t.val+1) next a=v.wireUsedAt h width t.val (StockBound.state C initial t.val) a+
      v.wireWithdrawal h width ((es).get t) next a := by
  intro next
  rw [v.wire_used_preserved h width initial runReady word (t.val+1) t.isLt a,
    v.wire_used_preserved h width initial runReady word t.val t.isLt.le a,
    v.wire_withdrawal_at_prefix h width initial runReady word t (t.val+1) (Nat.lt_succ_self _) t.isLt a]
  exact v.wire_used_next h width t (checkedOut C flag initial) a

/-- The owner and width arrays in the original wire presentation enumerate
the same chronological records as the signed reserve scatter. -/
theorem wire_used_checkout (initial : Memory w) (runReady : Calendar.mounted C es initial) (widthFits : width<2^w)
    (dates : Dates C initial L base num width) (j : ℕ) (a : pairs) :
    let issued:=CatalystArchive.issued dates
    let m:=checkedOut C flag initial
    v.wireUsedAt h width j m a=usedBeforeDate v.mesh issued (nativeSite L v.mesh issued capPos m) j (keys a) := by
  intro issued m
  have shape (t : Fin (es).length) : (atTime v.mesh issued t).rows=(L).rows ((es).get t) :=
    issued_shape dates t (fun _=> rfl)
  have floor := fun e x hx=>(v.event_prefix P h width r old (TerminalLayout.source page)
    (TerminalLayout.table page) (TerminalLayout.destination page) (sinkBank start cnt r rows) e x hx).1
  have output (t : Fin (es).length) (i : Fin (atTime v.mesh issued t).rows) :
      (m (base ((es).get t)+i.val)).val=(atTime v.mesh issued t).bits i := by
    let ev:=(es).get t
    have arity : (atTime v.mesh issued t).rows=(L).rows ev:=shape t
    have fit : base ev+i.val<(A).base v.mesh ev+(A).stride := by
      cases here : ev with
      | feed b =>
        have no : (atTime v.mesh issued t).rows=0:=arity.trans (congrArg (L).rows here)
        have hi:=i.isLt
        omega
      | attempt b =>
        exact v.debit_room h width b (Fin.cast (arity.trans (congrArg (L).rows here)) i)
    have bound := (A).within v.mesh ev ((es).get_mem t)
    have cell := dated_word C A initial flag runReady floor t (base ev+i.val) fit (ne_of_lt (fit.trans_le bound))
    exact (congrArg Fin.val (cell.trans (issued_cash dates t i))).trans
      (Fin.val_cast_of_lt (((atTime v.mesh issued t).fits i).trans_lt widthFits))
  let ownerAt := fun ev (i : ℕ) => CatalystArchive.key capPos (((L).term ev).eval m (i:Word w))
  let amount := fun ev i => (m (base ev+i)).val
  have agree (ev : Event) : v.wireWithdrawal h width ev m a=ownerWithdrawal (L).rows ownerAt amount ev (keys a) := by
    cases ev <;> rfl
  change (((es).take j).map (fun ev=> v.wireWithdrawal h width ev m a)).sum=_
  simp_rw [agree]
  exact ownerWithdrawal_prefix (L).rows ownerAt amount v.mesh issued j (keys a) shape output

/-- A positive cell is routed to the owner stored by its original typed
packet, including earlier purchased tiles read through their parent shelf. -/
theorem wire_positive_site (initial : Memory w) (runReady : Calendar.mounted C es initial)
    (word : flag<2^w) (countFits : num<2^w) (dates : Dates C initial L base num width) :
    let issued:=CatalystArchive.issued dates
    let chk:=checkedOut C flag initial
    ∀i,0 < debit v.mesh issued i→nativeSite L v.mesh issued capPos chk i=site v.mesh issued i := by
  intro issued chk
  have floor (e : Event) (x : ℕ) (hx : x<(A).base v.mesh e) := (v.event_prefix P h width r old
    (TerminalLayout.source page) (TerminalLayout.table page) (TerminalLayout.destination page)
    (sinkBank start cnt r rows) e x hx).1
  exact nativeSite_from_portROM C A initial flag L issued capPos countFits runReady floor
    (v.catalyst_owner_args h width (WideMemory.K h v.W) (directory).groups (WideMemory.H h v.W k v.wideJobs)
      (WideMemory.R v.sampler h v.W k) (P).joint (P).catalogue (v.wideSources h width).2 own
      (v.wideGeometryPrefix h width).2.2 word)
    (fun z=>(Nat.le_add_right ..).trans ((A).within v.mesh _ ((es).get_mem z))) (issued_port dates)

/-- A reserve delta on the actual next memory is the sum of the selected
histogram debits for this physical column and axis, identified by the
original typed `Date` owners. Rows with zero debit require no owner. -/
theorem wire_selected_delta (initial : Memory w) (runReady : Calendar.mounted C es initial)
    (word : flag<2^w) (countFits : num<2^w) (widthFits : width<2^w)
    (dates : Dates C initial L base num width) (t : Fin (es).length) (a : pairs) :
    let issued:=CatalystArchive.issued dates
    let entry:=atTime v.mesh issued t
    let next:=StockBound.state C initial (t.val+1)
    v.wireWithdrawal h width ((es).get t) next a=
      ∑ i : Fin entry.rows, if entry.owner i=keys a then entry.bits i else 0 := by
  intro issued entry next
  let chk:=checkedOut C flag initial
  let indexed:=nativeSite L v.mesh issued capPos chk
  have ownership:=v.wire_positive_site h width initial runReady word countFits dates
  have cumulative:=v.wire_used_next h width t chk a
  rw [v.wire_used_checkout h width initial runReady widthFits dates (t.val+1) a,
    v.wire_used_checkout h width initial runReady widthFits dates t.val a,
    usedBefore_succ v.mesh issued indexed t (keys a)] at cumulative
  rw [v.wire_withdrawal_at_prefix h width initial runReady word t (t.val+1) (Nat.lt_succ_self _) t.isLt a,
    ← Nat.add_left_cancel cumulative]
  unfold withdrawn
  apply Finset.sum_congr rfl
  intro i _
  by_cases charged : 0 < entry.bits i
  · have positive : 0 < debit v.mesh issued (rank v.mesh issued ⟨t,i⟩) := by
      rw [CatalystArchive.debit_at_rank v.mesh issued t i]
      exact charged
    have hit : indexed (rank v.mesh issued ⟨t,i⟩)=entry.owner i := by
      let owner := fun x : (Σ z, Fin (atTime v.mesh issued z).rows) => (atTime v.mesh issued x.1).owner x.2
      exact (ownership (rank v.mesh issued ⟨t,i⟩) positive).trans
        (congrArg owner ((rank v.mesh issued).symm_apply_apply ⟨t,i⟩))
    rw [hit]
  · have zero : (atTime v.mesh issued t).bits i=0:=Nat.eq_zero_of_not_pos charged
    simp [zero,entry]

set_option maxRecDepth 8192 in
set_option cleanup.letToHave false in
set_option maxHeartbeats 2000000 in
/-- This is the rank-filtered sum written verbatim in the physical per-date
reserve replay, with the original economic owner at every charged occurrence. -/
theorem wire_replay_rows (initial : Memory w) (runReady : Calendar.mounted C es initial)
    (word : flag<2^w) (countFits : num<2^w) (widthFits : width<2^w)
    (dates : Dates C initial L base num width) (j : ℕ) (bounded : j≤(es).length) (a : pairs) :
    let issued:=CatalystArchive.issued dates
    v.wireUsedAt h width j (StockBound.state C initial j) a=
      ∑i : Fin (recordCount v.mesh issued),
        if ((rank v.mesh issued).symm i).1.val < j ∧ site v.mesh issued i=keys a then debit v.mesh issued i else 0 := by
  intro issued
  rw [v.wire_used_preserved h width initial runReady word j bounded a,
    v.wire_used_checkout h width initial runReady widthFits dates j a,usedBefore_rows]
  apply Finset.sum_congr rfl
  intro i _
  by_cases charged : 0 < debit v.mesh issued i
  · rw [v.wire_positive_site h width initial runReady word countFits dates i charged]
  · dsimp only [issued] at charged ⊢
    simp [Nat.eq_zero_of_not_pos charged]

theorem wire_countAt (initial : Memory w) (runReady : Calendar.mounted C es initial)
    (word : flag<2^w) (countFits : num<2^w) (widthFits : width<2^w)
    (dates : Dates C initial L base num width) (j : ℕ) (bounded : j≤(es).length) (a : pairs) :
    let issued:=CatalystArchive.issued dates
    v.wireUsedAt h width j (StockBound.state C initial j) a=PrefixReserve.used (site v.mesh issued)
      (debit v.mesh issued) (PrefixReserve.countAt v.mesh issued j) (keys a) :=
  (v.wire_replay_rows h width initial runReady word countFits widthFits dates j bounded a).trans
    (PrefixReserve.chronological v.mesh _ j (keys a)).symm

/-- The actual prefix withdrawal is bounded by the initial reserve at every
column and axis. At the last date it equals the observed used-bank counter. -/
theorem wire_reserve_dated (initial : Memory w) (runReady : Calendar.mounted C es initial)
    (word : flag<2^w) (widthFits : width<2^w) (dates : Dates C initial L base num width)
    {I : Type*} [Fintype I] (paths : I→List (Fin rows)) (centers : pairs→List (Fin rows))
    (order : Fin r≃RouteOccurrence paths centers) (ci : I→ℕ) (arch : ReserveUse.Archive)
    (mem : Memory w)
    (R : Whole.Reconciliation sink arch supply (nativeSite L v.mesh (CatalystArchive.issued dates) capPos
      (checkedOut C flag initial)) (debit v.mesh (CatalystArchive.issued dates)) order ci keys mem) (a : pairs) :
    (∀j, j≤(es).length → v.wireUsedAt h width j (StockBound.state C initial j) a ≤ supply) ∧
      v.wireUsedAt h width (es).length (checkedOut C flag initial) a=R.usedAt a := by
  let src:=CatalystArchive.issued dates
  let ownAt:=nativeSite L v.mesh src capPos (checkedOut C flag initial)
  have balance:=R.funded (keys a)
  constructor
  · intro j hj
    rw [v.wire_used_preserved h width initial runReady word j hj a,
      v.wire_used_checkout h width initial runReady widthFits dates j a]
    exact usedBefore_le v.mesh src ownAt (keys a) j balance
  · rw [v.wire_used_checkout h width initial runReady widthFits dates (es).length a,usedBefore_last]
    exact (ReserveUse.reported arch (sink).banks supply ownAt (debit v.mesh src) mem R.archive (keys a)
      R.usedSize R.reserveSize balance R.word).1.symm

/-- The step reindexes the original typed date directly to the paid pair.
The word bound follows from the same settlement bank used to read the final reserve. -/
theorem wire_step_dated (initial : Memory w) (runReady : Calendar.mounted C es initial)
    (word : flag<2^w) (pageRoom : 28*2^page<2^w) (widthFits : width<2^w)
    (dates : Dates C initial L base num width)
    {I : Type*} [Fintype I] (paths : I→List (Fin rows)) (centers : pairs→List (Fin rows))
    (order : Fin r≃RouteOccurrence paths centers) (ci : I→ℕ) (arch : ReserveUse.Archive)
    (mem : Memory w)
    (R : Whole.Reconciliation sink arch supply (nativeSite L v.mesh (CatalystArchive.issued dates) capPos
      (checkedOut C flag initial)) (debit v.mesh (CatalystArchive.issued dates)) order ci keys mem)
    (t : Fin (es).length) (a : pairs) :
    let entry:=atTime v.mesh (CatalystArchive.issued dates) t
    let oldUsed:=v.wireUsedAt h width t.val (StockBound.state C initial t.val) a
    let afterUsed:=v.wireUsedAt h width (t.val+1) (StockBound.state C initial (t.val+1)) a
    let delta:=∑ i : Fin entry.rows,if entry.owner i=keys a then entry.bits i else 0
    afterUsed=oldUsed+delta ∧ delta ≤ supply-oldUsed ∧ supply-oldUsed=delta+(supply-afterUsed) := by
  intro entry oldUsed afterUsed delta
  have countRoom : num < 2^w := by
    have cap : num≤2^page:=R.usedSize
    omega
  have stable:=v.wire_used_retired_step h width initial runReady word t a
  have cost:=v.wire_selected_delta h width initial runReady word countRoom widthFits dates t a
  change afterUsed=oldUsed+_ at stable
  rw [cost] at stable
  have full:=v.wire_reserve_dated h width initial runReady word widthFits dates paths centers order ci arch mem R a
  have bound : afterUsed ≤ supply:=full.1 (t.val+1) t.isLt
  have settle (after before charge cap : ℕ) (step : after = before + charge) (bounded : after ≤ cap) :
      after = before + charge ∧ charge ≤ cap-before ∧ cap-before = charge+(cap-after) := by omega
  exact settle afterUsed oldUsed delta _ stable bound

set_option maxRecDepth 8192
set_option cleanup.letToHave false
set_option maxHeartbeats 2000000
attribute [local irreducible] CatalystArchive.recordCount CatalystArchive.issued
  CatalystArchive.nativeSite CatalystArchive.debit
  ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec
private theorem wireReserveEndpoint (initial : Memory w) (runReady : Calendar.mounted C es initial)
    (word : flag<2^w) (widthFits : width<2^w) (dates : Dates C initial L base num width)
    {I : Type*} [Fintype I] (paths : I→List (Fin rows)) (centers : pairs→List (Fin rows))
    (order : Fin r≃RouteOccurrence paths centers) (ci : I→ℕ) (arch : ReserveUse.Archive)
    (mem : Memory w)
    (R : Whole.Reconciliation sink arch supply (nativeSite L v.mesh (CatalystArchive.issued dates) capPos
      (checkedOut C flag initial)) (debit v.mesh (CatalystArchive.issued dates)) order ci keys mem) (a : pairs) :
    (∀j, j≤(es).length → v.wireUsedAt h width j (StockBound.state C initial j) a ≤ supply) ∧
      v.wireUsedAt h width (es).length (checkedOut C flag initial) a=R.usedAt a ∧
      v.wireUsedAt h width (es).length (StockBound.state C initial (es).length) a=R.usedAt a := by
  have bound:=v.wire_reserve_dated h width initial runReady word widthFits dates
    paths centers order ci arch mem R a
  exact ⟨bound.1, bound.2,
    (v.wire_used_preserved h width initial runReady word (es).length le_rfl a).trans bound.2⟩

-- The record count identifies the dates actually selected by the funded execution.
-- Pass their route family and archive directly to the dated endpoint theorem.
open Lean Elab Tactic in
local elab "applyReserveReceipt " fn:ident inst:ident cert:ident keyOperand:ident : tactic => withMainContext do
  let f ← Meta.getFVarFromUserName fn.getId
  let commodityInstance ← Meta.getFVarFromUserName inst.getId
  let receipt ← Meta.getFVarFromUserName cert.getId
  let pairOperand ← Meta.getFVarFromUserName keyOperand.getId
  let t ← Meta.whnf (← Meta.inferType receipt)
  unless t.getAppFn.isConstOf ``Whole.Reconciliation do
    throwError "expected a reserve reconciliation"
  let #[_, _, _, IOperand, _, pathsOperand, centersOperand, rowsOperand, _, _, archiveOperand, _, _, _, orderOperand, ciOperand, _, memOperand] := t.getAppArgs
    | throwError "unexpected reconciliation arguments"
  let rowCount ← Meta.whnf rowsOperand
  unless rowCount.getAppFn.isConstOf ``CatalystArchive.recordCount do
    throwError "expected a count of issued reserve records"
  let issued ← Meta.whnf rowCount.getAppArgs.back!
  unless issued.getAppFn.isConstOf ``CatalystArchive.issued do
    throwError "expected the issued reserve records"
  let dates := issued.getAppArgs.back!
  let app := mkAppN f #[dates, IOperand, commodityInstance, pathsOperand, centersOperand, orderOperand,
    ciOperand, archiveOperand, memOperand, receipt, pairOperand]
  (← getMainGoal).assign app
  replaceMainGoal []

private abbrev reserveStatement (size bits : ℕ) (extent : v.wideFundedSize h width bits ≤ size)
    (height : v.wideFundedHeight ≤ h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (state : Word w) (a : pairs) : Prop :=
    let tape:=v.wideFundedRaw h width bits raw
    let mid:=v.wideSignedMidAt h width size stock v.radius π (wideRouteOrder h D k) tape
    let chk:=v.wideSignedCheckoutAt h width size stock v.radius π (wideRouteOrder h D k) tape
    let paid:=Classical.choose_spec (v.wide_funded_run_at h width v.radius π raw bits size extent height budget small state)
    (∀j,j≤(es).length → v.wireUsedAt h width j (StockBound.state C mid j) a ≤ supply) ∧
      v.wireUsedAt h width (es).length chk a=Whole.Reconciliation.usedAt
        (I := Commodity (Fin (2^h)) (Stages h (2^v.W)) k) (J := Columns h (2^v.W) × Fin k) paid.1 a ∧
      v.wireUsedAt h width (es).length (StockBound.state C mid (es).length) a=Whole.Reconciliation.usedAt
        (I := Commodity (Fin (2^h)) (Stages h (2^v.W)) k) (J := Columns h (2^v.W) × Fin k) paid.1 a

/-- Every input selector history starts with the same per-column reserve. On
the original funded execution, any prefix respects that reserve, and the last
prefix agrees with the physical native counter. -/
theorem wide_wire_reserve (size bits : ℕ) (extent : v.wideFundedSize h width bits ≤ size)
    (height : v.wideFundedHeight ≤ h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (state : Word w) (a : pairs) :
    reserveStatement v h width size bits extent height budget small π raw state a := by
  unfold reserveStatement
  intro tape mid chk paid
  let receipt := paid.1
  have whole:=(v.wide_funded_stock_at_size h width v.radius π raw bits size extent height budget small).mounted_all
  have fit:=(v.wide_stock_sizes h width ((le_max_right ..).trans height) budget small).words.addresses
  have widthFits:=small.trans_lt (v.date_prefix_fit h)
  let endpoint := @wireReserveEndpoint.{0} F _ k p q Q σ Λ v h width mid whole fit widthFits
  let commodityFintype : Fintype (Commodity (Fin (2^h)) (Stages h (2^v.W)) k) := inferInstance
  applyReserveReceipt endpoint commodityFintype receipt a


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

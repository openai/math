import OAI.Hierarchy.ProtocolRAMStockCommitDebit
import OAI.Hierarchy.ProtocolRAMCalendarFrozen
import OAI.Hierarchy.ProtocolRAMCalendarCash

namespace OAI
/-! # Pricing the archived words of the actually executed stock commit -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {w q d rows paths : ℕ}

namespace StockCommit

theorem read_broadcast (s : StockCommit) (b : Batch q d) (m : Memory w) (j : Fin rows)
    (ready : (s.native w rows b).ready m) (fits : (RepairHistogram.broadcastTerm b s.price).Fits w s.direct)
    (qFit : q≤2^w) (copyFit : b.copies<2^w) (sumFit : q*b.copies<2^w)
    (keep : RepairHistogram.commit_keeps s.plan s.occurrences s.goods (s.broadcast+j.val)) :
    (s.native w rows b).after m (s.broadcast+j.val) = if RepairHistogram.committed b m (j.val:Word w)
        then s.price.read m (b.packet.eval m (j.val:Word w)) else 0 := by
  let base := result (RepairHistogram.directColumns s.direct s.occurrences s.goods s.plan s.columns) m
  let after := s.beforeApply b rows m
  have first (x : ℕ) (hx : x<s.direct) : base x=m x := by
    apply result_below
    intro p hp
    simp only [RepairHistogram.directColumns,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> simp only <;> omega
  have kept : (s.native w rows b).after m (s.broadcast+j.val)=after (s.broadcast+j.val) :=
    RepairHistogram.commit_frame s.columns s.plan _ _ after _ ready.2.2 keep
  rw [kept]
  change image s.broadcast rows (RepairHistogram.broadcastTerm b s.price) base (s.broadcast+j.val)=_
  rw [ProtocolRAMGeneratedWrite.read_image,eval_below _ _ m base fits first,
    RepairHistogram.broadcastTerm_eval b s.price m _ qFit copyFit sumFit]

/-- The signed-detector snapshot and the sparse-update snapshot retain identical
resource addresses and charged word amounts across quote archiving. -/
theorem sparse_inputs (s : StockCommit) (b : Batch q d) (m : Memory w) (order : s.direct≤ s.broadcast)
    (address : s.columns.destination.Fits w s.direct) (credit : s.columns.credit.Fits w s.direct)
    (debit : s.columns.charge.Fits w s.direct) :
    let u := s.beforeApply b rows m
    RepairHistogram.kind (n:=s.occurrences) (goods:=s.goods) s.plan.bank s.columns u=
       RepairHistogram.kind s.plan.bank s.columns m ∧
    RepairHistogram.installedBits (n:=s.occurrences) s.columns u=RepairHistogram.installedBits s.columns m ∧
    RepairHistogram.consumedBits (n:=s.occurrences) s.columns u=RepairHistogram.consumedBits s.columns m := by
  have dest : RepairHistogram.address (n:=s.occurrences) s.columns (s.beforeApply b rows m)=RepairHistogram.address s.columns m := by
    funext e
    exact congrArg Fin.val (s.inputs_beforeApply b m order _ address (e.val:Word w))
  refine ⟨?_,?_,?_⟩
  · funext e
    simp only [RepairHistogram.kind,dest]
  · funext e
    exact congrArg Fin.val (s.inputs_beforeApply b m order _ credit (e.val:Word w))
  · funext e
    exact congrArg Fin.val (s.inputs_beforeApply b m order _ debit (e.val:Word w))

/-- Financial and physical readbacks at both ends of a real calendar commit. The
old balance is the one used by the detector before any event words were appended. -/
theorem repair_receipt (s : StockCommit) (b : Batch q d) (m : Memory w) (i : Fin s.goods)
    (ready : (s.native w rows b).ready m) (order : s.direct≤ s.broadcast)
    (address : s.columns.destination.Fits w s.direct) (credit : s.columns.credit.Fits w s.direct)
    (debit : s.columns.charge.Fits w s.direct) (seed : s.plan.bank.base+s.goods≤ s.direct)
    (space : s.plan.bank.base+s.goods≤ s.plan.src) (wide : 4≤2^w) (payload cap : ℕ) (limit : s.plan.limit=cap*payload)
    (room : s.plan.limit<2^w) (excess : s.plan.excess.base=s.plan.clip.base+s.goods)
    (clipCap : s.goods≤ s.plan.clip.size) (excessCap : s.goods≤ s.plan.excess.size) (bankCap : s.goods≤ s.plan.bank.size)
    (funded : OuterBank.resourceBits (RepairHistogram.kind s.plan.bank s.columns m)
       (RepairHistogram.consumedBits (n:=s.occurrences) s.columns m) i≤(m (s.plan.bank.base+i.val)).val)
    (fit : (m (s.plan.bank.base+i.val)).val+OuterBank.resourceBits (RepairHistogram.kind s.plan.bank s.columns m)
       (RepairHistogram.installedBits (n:=s.occurrences) s.columns m) i<2^w)
    (mode : (s.plan.mode.eval (RepairHistogram.beforeTransfer s.columns s.plan s.occurrences s.goods
          (s.beforeApply b rows m)) (i.val:Word w)).val=2) :
    let actual := s.beforeApply b rows m
    let raw := RepairHistogram.raw s.plan.bank s.columns s.plan.src s.occurrences actual
    let out := (s.native w rows b).after m
    (m (s.plan.bank.base+i.val)).val+OuterBank.resourceBits (RepairHistogram.kind s.plan.bank s.columns m)
       (RepairHistogram.installedBits (n:=s.occurrences) s.columns m) i = raw i+
       OuterBank.resourceBits (RepairHistogram.kind s.plan.bank s.columns m) (RepairHistogram.consumedBits (n:=s.occurrences) s.columns m) i ∧
    (out (s.plan.activeOut+i.val)).val=min (raw i) (cap*payload) ∧
    (out (s.plan.activeOut+s.goods+s.goods+i.val)).val=spillBits cap payload raw i := by
  let u := s.beforeApply b rows m
  obtain ⟨same,inst,cons⟩ := s.sparse_inputs (rows:=rows) b m order address credit debit
  change RepairHistogram.kind (n:=s.occurrences) (goods:=s.goods) s.plan.bank s.columns u = _ at same
  change RepairHistogram.installedBits (n:=s.occurrences) s.columns u = _ at inst
  change RepairHistogram.consumedBits (n:=s.occurrences) s.columns u = _ at cons
  have first : u (s.plan.bank.base+i.val)=m (s.plan.bank.base+i.val) :=
    s.beforeCore b m order _ (by have := i.isLt;omega)
  have balance := RepairHistogram.balance s.plan.bank s.columns s.plan.src s.occurrences u i space
    (by simpa only [same,cons,first] using funded) (by simpa only [same,inst,first] using fit)
  refine ⟨by simpa only [same,cons,inst,first] using balance,?_⟩
  exact RepairHistogram.commit_repair s.columns s.plan u ready.2.1 i wide payload cap limit room excess clipCap excessCap bankCap mode

theorem delta_beforeApply (s : StockCommit) (b : Batch q d) (m : Memory w) (order : s.direct≤ s.broadcast)
    (credit : s.columns.credit.Fits w s.direct) (debit : s.columns.charge.Fits w s.direct) (e : Fin s.occurrences) :
    RepairHistogram.delta s.columns (s.beforeApply b rows m) e=RepairHistogram.delta s.columns m e := by
  simp only [RepairHistogram.delta,s.inputs_beforeApply (rows:=rows) b m order _ credit,
    s.inputs_beforeApply (rows:=rows) b m order _ debit]

theorem mode_beforeApply (s : StockCommit) (b : Batch q d) (m : Memory w) (order : s.direct≤ s.broadcast)
    (cut : ℕ) (fits : s.plan.mode.Fits w cut) (loc : cut≤ s.direct ∧ cut≤ s.plan.src ∧ cut≤ s.plan.clip.base)
    (safe : ∀ e : Fin s.occurrences, cut≤RepairHistogram.address s.columns (s.beforeApply b rows m) e)
    (r : Word w) : s.plan.mode.eval (RepairHistogram.beforeTransfer s.columns s.plan s.occurrences s.goods (s.beforeApply b rows m)) r=
      s.plan.mode.eval m r := by
  apply eval_below _ _ _ _ fits
  intro x hx
  exact (RepairHistogram.input_frame s.columns s.plan (s.beforeApply b rows m) x
    (hx.trans_le loc.2.1) (hx.trans_le loc.2.2) (fun e => (hx.trans_le (safe e)).ne')).trans
    (s.beforeCore b m order x (hx.trans_le loc.1))

theorem buy_receipt (s : StockCommit) (b : Batch q d) (m : Memory w) (i : Fin s.goods)
    (ready : (s.native w rows b).ready m) (order : s.direct≤ s.broadcast)
    (credit : s.columns.credit.Fits w s.direct) (debit : s.columns.charge.Fits w s.direct)
    (before : s.plan.bank.base+s.goods≤ s.direct) (space : s.plan.bank.base+s.goods≤ s.plan.src)
    (fresh : s.plan.bank.base+s.goods≤ s.plan.clip.base) (wide : 4≤2^w) (cap : s.goods≤ s.plan.bank.size)
    (idle : ∀ e : Fin s.occurrences,RepairHistogram.delta s.columns m e=0)
    (mode : let src := RepairHistogram.beforeTransfer s.columns s.plan s.occurrences s.goods (s.beforeApply b rows m)
      (s.plan.mode.eval src (i.val:Word w)).val=3)
    (half : let src := RepairHistogram.beforeTransfer s.columns s.plan s.occurrences s.goods (s.beforeApply b rows m)
      let x := s.plan.bank.read src (i.val:Word w)
      (s.plan.half.read src x).val=x.val/2) :
    let out := (s.native w rows b).after m
    let old := (m (s.plan.bank.base+i.val)).val
    (out (s.plan.activeOut+i.val)).val=old/2 ∧ (out (s.plan.activeOut+s.goods+i.val)).val=old-old/2 ∧
      out (s.plan.activeOut+s.goods+s.goods+i.val)=0 := by
  let u := s.beforeApply b rows m
  have preserve : u (s.plan.bank.base+i.val)=m (s.plan.bank.base+i.val) :=
    s.beforeCore b m order _ (by have := i.isLt;omega)
  have h := RepairHistogram.commit_buy s.columns s.plan u ready.2.1 i wide space fresh cap
    (fun e => (s.delta_beforeApply b m order credit debit e).trans (idle e)) mode half
  dsimp only
  rw [show (s.native w rows b).after m = RepairHistogram.commitOut s.columns s.plan s.occurrences s.goods u from rfl]
  simpa only [preserve] using h

theorem copy_receipt (s : StockCommit) (b : Batch q d) (m : Memory w) (i : Fin s.goods)
    (ready : (s.native w rows b).ready m) (order : s.direct≤ s.broadcast)
    (credit : s.columns.credit.Fits w s.direct) (debit : s.columns.charge.Fits w s.direct)
    (before : s.plan.bank.base+s.goods≤ s.direct ∧ s.plan.reserve.base+s.goods≤ s.direct)
    (space : s.plan.bank.base+s.goods≤ s.plan.src ∧ s.plan.reserve.base+s.goods≤ s.plan.src)
    (fresh : s.plan.bank.base+s.goods≤ s.plan.clip.base ∧ s.plan.reserve.base+s.goods≤ s.plan.clip.base)
    (wide : 4≤2^w) (cap : s.goods≤ s.plan.bank.size ∧ s.goods≤ s.plan.reserve.size)
    (apart : s.plan.bank.base+s.goods<s.plan.reserve.base ∨ s.plan.reserve.base+s.goods≤ s.plan.bank.base)
    (idle : ∀ e : Fin s.occurrences,RepairHistogram.delta s.columns m e=0)
    (mode : let src := RepairHistogram.beforeTransfer s.columns s.plan s.occurrences s.goods (s.beforeApply b rows m)
      (s.plan.mode.eval src (i.val:Word w)).val≠2 ∧ (s.plan.mode.eval src (i.val:Word w)).val≠3) :
    let out := (s.native w rows b).after m
    out (s.plan.activeOut+i.val)=m (s.plan.bank.base+i.val) ∧
      out (s.plan.activeOut+s.goods+i.val)=m (s.plan.reserve.base+i.val) ∧ out (s.plan.activeOut+s.goods+s.goods+i.val)=0 := by
  let u := s.beforeApply b rows m
  have h := i.isLt
  have first : u (s.plan.bank.base+i.val)=m (s.plan.bank.base+i.val) := s.beforeCore b m order _ (by omega)
  have remain : u (s.plan.reserve.base+i.val)=m (s.plan.reserve.base+i.val) := s.beforeCore b m order _ (by omega)
  have same := RepairHistogram.commit_copy s.columns s.plan u ready.2.1 i wide space.1 fresh.1 cap.1 cap.2 ⟨space.2,fresh.2⟩
    (fun e => by
      have guard := ready.2.2 e
      change s.plan.bank.base ≤ RepairHistogram.address s.columns u e ∧
        RepairHistogram.address s.columns u e ≤ s.plan.bank.base+s.goods at guard
      rcases apart with low | high <;> omega)
    (fun e => (s.delta_beforeApply b m order credit debit e).trans (idle e)) mode
  dsimp only
  rw [show (s.native w rows b).after m = RepairHistogram.commitOut s.columns s.plan s.occurrences s.goods u from rfl]
  simpa only [first,remain] using same

/-- Purchase fees use the mode-gated archived flag. Each frozen greedy flag is
charged exactly on the branch that buys the probes. -/
theorem buy_flag (s : StockCommit) (L : PurchaseStage.Dispatch) (B : PurchaseStage.Repair q d)
    (m : Memory w) (j : Fin L.candidates)
    (plan : AuditReady (PurchaseStage.audits L B) (PurchaseStage.postSnapshot L B m)) (board : PurchaseStage.Board L B w)
    (wide : 4≤2^w) (fits : PurchaseStage.decisionBase L+L.candidates≤2^w) (padded : L.candidates≤2^B.decisionBits)
    (tests : PurchaseStage.decisionBase L+L.candidates≤B.tests.excess.out ∧
      PurchaseStage.decisionBase L+L.candidates≤B.tests.payload.out ∧ PurchaseStage.decisionBase L+L.candidates≤B.tests.discrepancy.out)
    (sep : PurchaseStage.decisionBase L+L.candidates≤B.repairBits.base)
    (mounted : (s.native w L.candidates (PurchaseStage.enabledBatch L B)).ready (PurchaseStage.postOutput L B m))
    (safe : (s.native w L.candidates (PurchaseStage.enabledBatch L B)).keeps (B.purchaseOut+j.val)) :
    let out := (s.native w L.candidates (PurchaseStage.enabledBatch L B)).after (PurchaseStage.postOutput L B m)
    out (B.purchaseOut+j.val)=if AttemptGate.actual B.policy (PurchaseStage.postSnapshot L B m)=3
       then m (PurchaseStage.decisionBase L+j.val) else 0 :=
  ((s.native w L.candidates (PurchaseStage.enabledBatch L B)).frame _ _ mounted safe).trans
    (PurchaseStage.post_flag L B m plan board wide fits padded j tests sep)

def eventColumns (s : StockCommit) (flags : ℕ) : RepairHistogram.CashColumns :=
  ⟨s.direct,s.broadcast,s.plan.activeOut+s.goods+s.goods,flags⟩

def eventWords (s : StockCommit) (flags : ℕ) (payload copies : ℕ)
    (keys : RepairHistogram.CashKeys s.occurrences rows s.goods paths)
    (link : Fin s.occurrences → ℕ → ℝ) (tree : Fin rows → ℕ → ℝ) (core : Fin s.goods → ℕ → ℝ)
    (fee : Fin paths → ℕ → ℝ) (e : RepairHistogram.CashEvent s.occurrences rows s.goods paths) : ChargeWord :=
  ⟨(s.eventColumns flags).addr e,keys.atRow e,RepairHistogram.keyedPrice payload copies link tree core fee e⟩

/-- The exact monetary increment accepted by `AccountColumns.append_executed` is the five
live transaction columns. The price-table key can vary from edge to edge in one tick. -/
theorem event_value (s : StockCommit) (flags : ℕ) (payload copies : ℕ) (m : Memory w)
    (keys : RepairHistogram.CashKeys s.occurrences rows s.goods paths) (link : Fin s.occurrences → ℕ → ℝ)
    (tree : Fin rows → ℕ → ℝ) (core : Fin s.goods → ℕ → ℝ) (fee : Fin paths → ℕ → ℝ) :
    (∑ e,(s.eventWords flags payload copies keys link tree core fee e).value payload m)=
      RepairHistogram.eventBill (s.eventColumns flags) m payload copies (fun e => link e (m (keys.link e)).val)
        (fun r => tree r (m (keys.broadcast r)).val) (fun i => core i (m (keys.core i)).val)
        (fun j => fee j (m (keys.buy j)).val) :=
  RepairHistogram.keyed_bill (s.eventColumns flags) keys m payload copies link tree core fee

/-- On the actual completed segment the newly appended price rows are the signed
ordinary-link bill, selector broadcast, routed overflow, and purchase fees. -/
theorem event_receipt (s : StockCommit) (b : Batch q d) (m : Memory w) (flags payload copies : ℕ)
    (positive : 0<payload) (ready : (s.native w rows b).ready m)
    (board : EventBoard s w)
    (keys : RepairHistogram.CashKeys s.occurrences rows s.goods paths) (link : Fin s.occurrences → ℕ → ℝ)
    (tree : Fin rows → ℕ → ℝ) (core : Fin s.goods → ℕ → ℝ) (fee : Fin paths → ℕ → ℝ) :
    let out := (s.native w rows b).after m
    (∑ e,(s.eventWords flags payload copies keys link tree core fee e).value payload out) =
      RepairHistogram.linkBill (goods:=s.goods) s.columns s.plan.bank m payload (fun e => link e (out (keys.link e)).val) +
        (∑ r,(copies:ℝ)*(tree r (out (keys.broadcast r)).val*(out (s.broadcast+r.val)).val))/payload +
        (∑ i,((out (s.plan.activeOut+s.goods+s.goods+i.val)).val:ℝ)/payload*core i (out (keys.core i)).val)+
        ∑ j,(out (flags+j.val)).val*fee j (out (keys.buy j)).val := by
  dsimp only
  rw [s.event_value]
  apply RepairHistogram.eventBill_eq _ _ _ _ _ _ _ positive
  exact fun e => s.read_direct b m e ready board.chargeFits board.order (board.hit b m ready e) board.bound (board.keep e)

/-- A failed repair charges no purchases. Routing the archived excess at its true
length is bounded by its commodity box, as in `OuterBank.FailedRows.paid`. -/
theorem failed_price (s : StockCommit) (b : Batch q d) (m : Memory w) (flags payload copies cap : ℕ)
    (positive : 0<payload) (ready : (s.native w rows b).ready m)
    (board : EventBoard s w)
    (keys : RepairHistogram.CashKeys s.occurrences rows s.goods paths) (link : Fin s.occurrences → ℕ → ℝ)
    (tree : Fin rows → ℕ → ℝ) (core : Fin s.goods → ℕ → ℝ) (fee : Fin paths → ℕ → ℝ)
    (box : Fin s.goods → ℝ) (cash : ℝ)
    (route : ∀ i,core i (((s.native w rows b).after m) (keys.core i)).val≤box i)
    (spill : ∀ i : Fin s.goods,(((s.native w rows b).after m) (s.plan.activeOut+s.goods+s.goods+i.val)).val=
      spillBits cap payload (RepairHistogram.raw s.plan.bank s.columns s.plan.src s.occurrences (s.beforeApply b rows m)) i)
    (disabled : ∀ j : Fin paths, ((s.native w rows b).after m) (flags+j.val)=0) :
    let out := (s.native w rows b).after m
    let price := fun e => link e (out (keys.link e)).val
    let broadcast := (∑ r,(copies:ℝ)*(tree r (out (keys.broadcast r)).val*(out (s.broadcast+r.val)).val))/payload
    let raw := RepairHistogram.raw s.plan.bank s.columns s.plan.src s.occurrences (s.beforeApply b rows m)
    cash+(∑ e,(s.eventWords flags payload copies keys link tree core fee e).value payload out) ≤
      cash+cashChange (RepairHistogram.kind (goods:=s.goods) s.plan.bank s.columns m)
        (netUnits payload (RepairHistogram.installedBits s.columns m) (RepairHistogram.consumedBits s.columns m)) price broadcast +
      pairing (bitStock payload (spillBits cap payload raw)) box := by
  dsimp only
  rw [s.event_receipt b m flags payload copies positive ready board keys link tree core fee]
  simp only [disabled,Fin.val_zero,Nat.cast_zero,zero_mul,Finset.sum_const_zero,add_zero]
  rw [RepairHistogram.linkBill_eq,←add_assoc]
  apply add_le_add le_rfl
  unfold pairing bitStock
  exact Finset.sum_le_sum (fun i _ => by rw [spill i]; exact mul_le_mul_of_nonneg_left (route i) (by positivity))

/-- With the failed-ball mask disabled and no overflow, entering the acquisition
branch charges exactly the purchased catalyst flags. Their widths start at zero. -/
theorem buy_price (s : StockCommit) (b : Batch q d) (m : Memory w) (flags payload copies : ℕ)
    (positive : 0<payload) (ready : (s.native w rows b).ready m)
    (board : EventBoard s w)
    (keys : RepairHistogram.CashKeys s.occurrences rows s.goods paths) (link : Fin s.occurrences → ℕ → ℝ)
    (tree : Fin rows → ℕ → ℝ) (core : Fin s.goods → ℕ → ℝ) (fee : Fin paths → ℕ → ℝ)
    (inactive : ∀ e : Fin s.occurrences,RepairHistogram.installedBits s.columns m e=0 ∧ RepairHistogram.consumedBits s.columns m e=0)
    (broadcast : ∀ r : Fin rows, ((s.native w rows b).after m) (s.broadcast+r.val)=0)
    (spill : ∀ i : Fin s.goods, ((s.native w rows b).after m) (s.plan.activeOut+s.goods+s.goods+i.val)=0) :
    let out := (s.native w rows b).after m
    (∑ e,(s.eventWords flags payload copies keys link tree core fee e).value payload out)=
      ∑ j,(out (flags+j.val)).val*fee j (out (keys.buy j)).val := by
  dsimp only
  rw [s.event_receipt b m flags payload copies positive ready board keys link tree core fee]
  simp [RepairHistogram.linkBill,fun e => (inactive e).1,fun e => (inactive e).2,broadcast,spill]


end StockCommit
end
end Hierarchy.ProtocolRAM.Calendar

end OAI

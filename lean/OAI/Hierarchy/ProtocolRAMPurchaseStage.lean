import OAI.Hierarchy.ProtocolRAMPurchaseDispatch
import OAI.Hierarchy.ProtocolRAMStockAccounts
import OAI.Hierarchy.ProtocolRAMAttemptThresholds
import OAI.Hierarchy.ProtocolRAMVerdicts
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Audited purchase and repair at a fixed mesh tick

The failed-discrepancy branch uses the independent-set mask for local histogram
repairs. The purchase branch activates a disjoint set of zero-width ordinary
links from the greedy path scan and splits the outstanding inventory. A fixed
advance tick feeds the reserved slice and discharges the overflow. Stopped
ticks copy the inventory and reserve. All outputs retain their original row.
-/

namespace Hierarchy.ProtocolRAM.PurchaseStage

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators

variable {q d w : ℕ}

structure Repair (q d : ℕ) where
  batch : Batch q d
  decisionBits : ℕ
  tests : AttemptGate.TestBoard
  modeOut : ℕ
  failedMIS : Bank
  repairBits : Bank
  purchaseOut : ℕ
  boughtFields : Fin 7 → ℕ
  purchaseLink : Link
  purchaseMenu : Expr
  halfTable : Bank
  reserveOut : Fin d → ℕ
  feedOnAdvance : Bool
  keys : ℕ
  tally : ℕ
  verdict : ℕ
  quoteOut : ℕ
  priceOut : Fin batch.quotes.length → ℕ
  link : Link
  reportWidth : Fin q → Expr
  reportOut : Fin 7 → ℕ
  feedTable : Bank
  feedStride : ℕ
  mesh : ℕ
  reserve : Fin d → Expr
  wire : Fin d → Fin q → Expr
  cap : Fin d → ℕ
  stockOut : Fin d → ℕ

def Repair.policy (B : Repair q d) := B.tests.inputs

def tested (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w) :=
  B.tests.after (dispatchMemory L rows m)

def repairMask (B : Repair q d) : Expr :=
  AttemptGate.ifRepair B.policy (.lookup B.failedMIS B.batch.owner) (.lit 0)

def snapshot {w : ℕ} (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w) : Memory w :=
  image B.repairBits.base L.candidates (repairMask B) (tested L B rows m)

def enabledBatch (_L : Dispatch) (B : Repair q d) : Batch q d :=
  {B.batch with enabled := B.repairBits, owner := .row}

def buyWord (L : Dispatch) (B : Repair q d) : Expr :=
  AttemptGate.ifPurchase B.policy (.lookup ⟨decisionBase L,B.decisionBits⟩ .row) (.lit 0)

def inspection (L : Dispatch) (B : Repair q d) : Inspection :=
  ⟨q,d,enabledBatch L B,B.keys,B.tally,L.candidates⟩

/-- Purchasing a link records its immutable endpoints and identifier. Its initial width is zero. -/
def buyFields (L : Dispatch) (B : Repair q d) : Fin 7 → Expr :=
  ![B.purchaseLink.group,B.purchaseLink.endpoint,B.purchaseLink.opposite,
    .op .add (.lit B.purchaseLink.idBase) .row,.lit 0,B.purchaseLink.lengthCode,
    .branch .eq (buyWord L B) (.lit 0) (.lit 0) B.purchaseMenu]

/-- Feed only at a scheduled advance after the repairs at the current time. -/
def fedStock (B : Repair q d) (i : Fin d) : Expr :=
  feed B.feedTable B.feedStride B.mesh (B.reserve i) (B.batch.stock i)

def retained (L : Dispatch) (B : Repair q d) (i : Fin d) : Expr :=
  let b := enabledBatch L B
  let stock := b.stock i
  AttemptGate.ifRepair B.policy (b.nextStock i (b.wire (B.wire i)))
    (AttemptGate.ifPurchase B.policy (.lookup B.halfTable stock)
      (AttemptGate.ifAdvance B.policy
        (if B.feedOnAdvance then StockAccounts.clipped (B.cap i) (fedStock B i) else stock) stock))

def discharge (B : Repair q d) (i : Fin d) : Expr :=
  AttemptGate.ifAdvance B.policy
    (if B.feedOnAdvance then StockAccounts.overflow (B.cap i) (fedStock B i) else .lit 0) (.lit 0)

/-- The reserve is the original purchase remainder throughout the complete fixed mesh. -/
def saved (B : Repair q d) (i : Fin d) : Expr :=
  let stock := B.batch.stock i
  AttemptGate.ifPurchase B.policy (.op .sub stock (.lookup B.halfTable stock)) (B.reserve i)

def stockWrites (L : Dispatch) (B : Repair q d) (i : Fin d) : List Pass :=
  [⟨B.stockOut i,L.candidates,retained L B i⟩,
   ⟨B.stockOut i+L.candidates,L.candidates,discharge B i⟩,
   ⟨B.reserveOut i,L.candidates,saved B i⟩]

def priceColumns (L : Dispatch) (B : Repair q d) : List Pass :=
  List.ofFn fun k => ⟨B.priceOut k,L.candidates,B.batch.quotes[k.val]'k.isLt⟩

def writes (L : Dispatch) (B : Repair q d) : List Pass :=
  let b := enabledBatch L B
  ⟨B.quoteOut,L.candidates,b.packet⟩ :: ⟨B.purchaseOut,L.candidates,buyWord L B⟩ ::
    ⟨B.modeOut,L.candidates,AttemptGate.mode B.policy⟩ ::
    ((List.ofFn (fun j => ⟨B.reportOut j,L.candidates,B.link.fields b B.reportWidth j⟩) ++
      List.ofFn (fun j => ⟨B.boughtFields j,L.candidates,buyFields L B j⟩)) ++
      ((List.ofFn (stockWrites L B)).flatten ++ priceColumns L B))

def columns (ps : List Pass) : List Audit := ps.map fun p => .native (.column p)

def audits (L : Dispatch) (B : Repair q d) : List Audit :=
  .check (inspection L B) :: columns (writes L B)

/-- The executable bytecode is uniform over all marks, candidate paths and selector words. -/
def code (w : ℕ) (L : Dispatch) (B : Repair q d) : Procedure w :=
  (dispatch L w).seq ((B.tests.code w).seq ((scan w B.repairBits.base L.candidates (repairMask B)).seq
    (finalVerdict w B.verdict (audits L B))))

def ticks (L : Dispatch) (B : Repair q d) :=
  dispatchClock L + (B.tests.ticks + ((4+L.candidates*(2*(repairMask B).work+4)) +
    (auditTicks (audits L B) + (4+1*(2*(verdict (audits L B)).work+4)))))

noncomputable def output (L : Dispatch) (B : Repair q d) (rows : Fin L.candidates → Fin L.depth → Fin L.tiles)
    (m : Memory w) :=
  verdictMemory B.verdict (audits L B) (snapshot L B rows m)

attribute [local irreducible] CheapCode in
theorem cheap (w : ℕ) (L : Dispatch) (B : Repair q d) : CheapCode (code w L B) :=
  cheap_seq (A:=dispatch L w) (B:=(B.tests.code w).seq ((scan w B.repairBits.base L.candidates (repairMask B)).seq (finalVerdict w B.verdict (audits L B)))) (dispatch_cheap L w) (cheap_seq (A:=B.tests.code w) (B:=(scan w B.repairBits.base L.candidates (repairMask B)).seq (finalVerdict w B.verdict (audits L B))) (B.tests.cheap w)
    (cheap_seq (A:=scan w B.repairBits.base L.candidates (repairMask B)) (B:=finalVerdict w B.verdict (audits L B))
      (scan_cheap w B.repairBits.base L.candidates (repairMask B)) (finalVerdict_cheap w B.verdict (audits L B))))

private theorem admitted_columns (ps : List Pass) (m : Memory w) :
    AllAdmitted (columns ps) m := by
  induction ps generalizing m with
  | nil => trivial
  | cons p ps ih => exact ⟨True.intro, ih _⟩

def TestsReady (B : Repair q d) (v : Memory w) : Prop :=
  B.tests.excess.Ready v ∧ B.tests.payload.Ready (B.tests.excess.after v) ∧
    B.tests.discrepancy.Ready (B.tests.payload.after (B.tests.excess.after v))

/-- The flag validates selected histograms and requires the unselected rows' selector lanes
to be zero. The selected menu and available stocks are evaluated in the live post-mark state. -/
theorem exec (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w)
    (ready : DispatchReady L w) (table : PathTable L rows m) (signed : SignedWords L m)
    (tests : TestsReady B (dispatchMemory L rows m))
    (enableFits : (repairMask B).Fits w B.repairBits.base)
    (enableRoom : B.repairBits.base + L.candidates < 2^w)
    (plan : AuditReady (audits L B) (snapshot L B rows m))
    (order : OrderedTallies (audits L B))
    (deps : (verdict (audits L B)).Fits w B.verdict) (space : B.verdict+1<2^w) :
    (code w L B).Exec m (output L B rows m) (ticks L B) ∧
    (output L B rows m B.verdict = 0 ↔
      ∀ j<L.candidates, (enabledBatch L B).valid (snapshot L B rows m) (j:Word w)) := by
  have run := dispatch_exec L rows m ready table signed
  refine ⟨Procedure.Exec.then (A:=dispatch L w) run.1 (Procedure.Exec.then (A:=B.tests.code w)
    (B.tests.exec (dispatchMemory L rows m) tests.1 tests.2.1 tests.2.2)
    (Procedure.Exec.then (A:=scan w B.repairBits.base L.candidates (repairMask B))
      (B:=finalVerdict w B.verdict (audits L B))
      (scan_exec B.repairBits.base L.candidates (repairMask B) (tested L B rows m) enableFits enableRoom)
      (finalVerdict_exec (audits L B) B.verdict _ plan deps space))), ?_⟩
  have actual := finalVerdict_flag (audits L B) B.verdict _ plan order ready.width
  refine actual.trans ⟨fun h => h.1, fun h => ⟨h, admitted_columns _ _⟩⟩

/-- The local histogram repair uses only the failed-ball MIS. Selected path bits are kept
for the separate purchase output. The remaining tests read the actual stock and quoted menu. -/
theorem selected_iff (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w)
    (ready : DispatchReady L w) (padded : L.candidates ≤ B.repairBits.size) (j : Fin L.candidates) :
    let v := snapshot L B rows m
    let r : Word w := j.val
    (enabledBatch L B).selected v r ↔
      (repairMask B).eval (tested L B rows m) r ≠ 0 ∧ B.batch.packet.eval v r ≠ 0 ∧
      ∀ i, ((B.batch.need i).eval v r).val ≤ ((B.batch.stock i).eval v r).val := by
  have hr : j.val < 2^w := by have := ready.room; have := j.isLt; omega
  change B.repairBits.read (snapshot L B rows m) (j.val:Word w) ≠ 0 ∧ _ ∧ _ ↔ _
  rw [Bank.read,Fin.val_cast_of_lt hr,Nat.mod_eq_of_lt (j.isLt.trans_le padded)]
  rw [snapshot, ProtocolRAMGeneratedWrite.read_image]; rfl

theorem retained_eval (L : Dispatch) (B : Repair q d) (i : Fin d) (v : Memory w) (r : Word w)
    (wide : 4≤2^w) :
    let action := AttemptGate.actual B.policy v
    let stock := (B.batch.stock i).eval v r
    (retained L B i).eval v r =
      if action=2 then ((enabledBatch L B).nextStock i ((enabledBatch L B).wire (B.wire i))).eval v r
      else if action=3 then B.halfTable.read v stock
      else if action=1 ∧ B.feedOnAdvance = true then (StockAccounts.clipped (B.cap i) (fedStock B i)).eval v r
      else stock := by
  simp only [retained,AttemptGate.ifRepair,AttemptGate.ifPurchase,AttemptGate.ifAdvance,
    AttemptGate.ifMode_eval _ _ _ _ _ _ wide (by decide : 2<4),
    AttemptGate.ifMode_eval _ _ _ _ _ _ wide (by decide : 3<4),
    AttemptGate.ifMode_eval _ _ _ _ _ _ wide (by decide : 1<4),Expr.eval]
  cases h : B.feedOnAdvance <;> simp [enabledBatch]

theorem discharge_eval (B : Repair q d) (i : Fin d) (v : Memory w) (r : Word w) (wide : 4≤2^w) :
    (discharge B i).eval v r =
      if AttemptGate.actual B.policy v=1 ∧ B.feedOnAdvance = true
      then (StockAccounts.overflow (B.cap i) (fedStock B i)).eval v r else 0 := by
  simp only [discharge,AttemptGate.ifAdvance,AttemptGate.ifMode_eval _ _ _ _ _ _ wide (by decide : 1<4)]
  cases h : B.feedOnAdvance <;> simp [Expr.eval]

theorem saved_eval (B : Repair q d) (i : Fin d) (v : Memory w) (r : Word w) (wide : 4≤2^w) :
    let stock := (B.batch.stock i).eval v r
    (saved B i).eval v r = if AttemptGate.actual B.policy v=3 then stock-B.halfTable.read v stock
      else (B.reserve i).eval v r := by
  simp only [saved,AttemptGate.ifPurchase,AttemptGate.ifMode_eval _ _ _ _ _ _ wide (by decide : 3<4),
    Expr.eval, RowOp.opcode, BinaryOp.eval]

private theorem audit_append (xs ys : List Audit) (m : Memory w) :
    auditOut (xs++ys) m = auditOut ys (auditOut xs m) := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih => exact ih (x.out m)

private theorem ready_append (xs ys : List Audit) (m : Memory w) :
    AuditReady (xs++ys) m ↔ AuditReady xs m ∧ AuditReady ys (auditOut xs m) := by
  induction xs generalizing m with
  | nil => simp [AuditReady,auditOut]
  | cons x xs ih => simp [AuditReady,auditOut,ih,and_assoc]

/-- A column evaluated against the post-mark snapshot is still at its fixed address after
the audit and the return flag. The two bounds explicitly account for every intermediate write. -/
theorem column_at (L : Dispatch) (B : Repair q d) (v : Memory w)
    (before after : List Audit) (p : Pass) (j : Fin p.rows)
    (index : audits L B = before ++ .native (.column p) :: after)
    (plan : AuditReady (audits L B) v)
    (cut : ℕ) (inputs : p.term.Fits w cut) (early : ∀ a∈before, cut ≤ a.low)
    (later : ∀ a∈after, p.out+j.val < a.low) (flag : p.out+j.val < B.verdict) :
    verdictMemory B.verdict (audits L B) v (p.out+j.val) = p.term.eval v (j.val:Word w) := by
  let t := auditOut before v
  rw [index] at plan
  obtain ⟨pre, post⟩ := (ready_append before _ v).mp plan
  change image B.verdict 1 _ (auditOut (audits L B) v) _ = _
  rw [ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl flag),index,audit_append]
  change auditOut after (p.apply t) (p.out+j.val) = _
  have afterKeeps : auditOut after (p.apply t) (p.out+j.val)=(p.apply t) (p.out+j.val) :=
    audit_below after _ post.2 _ later
  rw [afterKeeps]
  change image p.out p.rows p.term t (p.out+j.val) = _
  rw [ProtocolRAMGeneratedWrite.read_image]
  exact eval_below _ _ v t inputs (fun k hk => audit_below before v pre k fun a ha =>
    hk.trans_le (early a ha))

/-- All outputs are written once in increasing order beyond the common input snapshot.
The final verdict uses its own later word. -/
structure Board (L : Dispatch) (B : Repair q d) (w : ℕ) : Prop where
  snapshot : ∃ cut ≤ B.keys,
    (∀ p ∈ writes L B, p.term.Fits w cut ∧ cut ≤ p.out)
  disjoint : (writes L B).Pairwise fun a b => a.out+a.rows ≤ b.out
  flagAfter : ∀ p ∈ writes L B, p.out+p.rows ≤ B.verdict

theorem read_at (L : Dispatch) (B : Repair q d) (v : Memory w)
    (plan : AuditReady (audits L B) v) (board : Board L B w)
    (p : Pass) (hp : p ∈ writes L B) (j : Fin p.rows) :
    verdictMemory B.verdict (audits L B) v (p.out+j.val) = p.term.eval v (j.val:Word w) := by
  obtain ⟨xs, ys, split⟩ := List.append_of_mem hp
  obtain ⟨cut, keys, inputs⟩ := board.snapshot
  have order := board.disjoint
  rw [split] at order
  refine column_at L B v (.check (inspection L B) :: columns xs) (columns ys) p j
    ?_ plan cut (inputs p hp).1 ?_ ?_ ?_
  · simp [audits, split, columns]
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact keys
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
      exact (inputs u (by rw [split]; exact List.mem_append_left _ hu)).2
  · intro a ha
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
    exact (Nat.add_lt_add_left j.isLt p.out).trans_le
      ((List.pairwise_cons.mp (List.pairwise_append.mp order).2.1).1 u hu)
  · exact (Nat.add_lt_add_left j.isLt p.out).trans_le (board.flagAfter p hp)

theorem read (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w)
    (plan : AuditReady (audits L B) (snapshot L B rows m)) (board : Board L B w)
    (p : Pass) (hp : p ∈ writes L B) (j : Fin p.rows) :
    output L B rows m (p.out+j.val) = p.term.eval (snapshot L B rows m) (j.val:Word w) :=
  read_at L B (snapshot L B rows m) plan board p hp j

theorem quote_read (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w)
    (plan : AuditReady (audits L B) (snapshot L B rows m)) (board : Board L B w)
    (j : Fin L.candidates) :
    output L B rows m (B.quoteOut+j.val) = B.batch.packet.eval (snapshot L B rows m) (j.val:Word w) :=
  read L B rows m plan board ⟨B.quoteOut,L.candidates,(enabledBatch L B).packet⟩ (List.mem_cons_self ..) j

/-- Every scalar price word entering the catalogue lookup is observable in the same
snapshot as the selected packet. -/
theorem price_read (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w)
    (plan : AuditReady (audits L B) (snapshot L B rows m)) (board : Board L B w)
    (j : Fin L.candidates) (k : Fin B.batch.quotes.length) :
    output L B rows m (B.priceOut k+j.val) =
      (B.batch.quotes[k.val]'k.isLt).eval (snapshot L B rows m) (j.val:Word w) := by
  apply read L B rows m plan board ⟨_,L.candidates,_⟩ _ j
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  apply List.mem_append_right
  exact List.mem_ofFn.mpr ⟨k,rfl⟩

/-- Both descriptor lists retain the original row index, including inactive rows. -/
theorem descriptor_read (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w)
    (plan : AuditReady (audits L B) (snapshot L B rows m)) (board : Board L B w)
    (j : Fin L.candidates) (k : Fin 7) :
    output L B rows m (B.reportOut k+j.val) =
      (B.link.fields (enabledBatch L B) B.reportWidth k).eval (snapshot L B rows m) (j.val:Word w) ∧
    output L B rows m (B.boughtFields k+j.val) = (buyFields L B k).eval (snapshot L B rows m) (j.val:Word w) := by
  constructor <;> apply read L B rows m plan board ⟨_,L.candidates,_⟩ _ j
  · apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_ofFn.mpr ⟨k,rfl⟩
  · apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_ofFn.mpr ⟨k,rfl⟩

theorem purchase_zero_width (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w)
    (plan : AuditReady (audits L B) (snapshot L B rows m)) (board : Board L B w)
    (j : Fin L.candidates) : output L B rows m (B.boughtFields 4+j.val)=0 :=
  (descriptor_read L B rows m plan board j 4).2

/-- Each original row exports the actual four-way control word of this tick. -/
theorem action_read (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w)
    (plan : AuditReady (audits L B) (snapshot L B rows m)) (board : Board L B w) (j : Fin L.candidates) :
    output L B rows m (B.modeOut+j.val) = (AttemptGate.actual B.policy (snapshot L B rows m) : Word w) :=
  (read L B rows m plan board ⟨_,L.candidates,AttemptGate.mode B.policy⟩
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) j).trans
    (AttemptGate.mode_eval ..)

theorem purchase_read (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w)
    (plan : AuditReady (audits L B) (snapshot L B rows m)) (board : Board L B w) (j : Fin L.candidates) :
    output L B rows m (B.purchaseOut+j.val) = (buyWord L B).eval (snapshot L B rows m) (j.val:Word w) :=
  read L B rows m plan board ⟨_,L.candidates,_⟩ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) j

/-- Only a true greedy path in the purchase branch pays for a new ordinary zero-width link. -/
theorem purchase_choice (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w)
    (ready : DispatchReady L w) (table : PathTable L rows m) (signed : SignedWords L m)
    (plan : AuditReady (audits L B) (snapshot L B rows m)) (board : Board L B w)
    (wide : 4≤2^w) (padded : L.candidates ≤ 2^B.decisionBits)
    (beforeChecks : decisionBase L+L.candidates ≤ B.tests.excess.out ∧
      decisionBase L+L.candidates ≤ B.tests.payload.out ∧ decisionBase L+L.candidates ≤ B.tests.discrepancy.out)
    (beforeEnable : decisionBase L+L.candidates ≤ B.repairBits.base) (j : Fin L.candidates) :
    let v := snapshot L B rows m
    let picked := (MarkTape.decisions (paths L rows) (marked L m))[j.val]'(by simp [paths])
    output L B rows m (B.purchaseOut+j.val) = if AttemptGate.actual B.policy v=3
      then MarkTape.encode w picked else 0 := by
  rw [purchase_read L B rows m plan board j]
  have hr : j.val < 2^w := by have := ready.room; have := j.isLt; omega
  simp only [buyWord,AttemptGate.ifPurchase,AttemptGate.ifMode_eval _ _ _ _ _ _ wide (by decide : 3<4),
    Expr.eval, Bank.read, Bank.size, Fin.val_cast_of_lt hr,Nat.mod_eq_of_lt (j.isLt.trans_le padded)]
  have row := Nat.add_lt_add_left j.isLt (decisionBase L)
  rw [show snapshot L B rows m (decisionBase L+j.val) = tested L B rows m (decisionBase L+j.val) from
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl (row.trans_le beforeEnable))]
  rw [show tested L B rows m (decisionBase L+j.val) = dispatchMemory L rows m (decisionBase L+j.val) from
    (B.tests.discrepancy.frame _ _ (row.trans_le beforeChecks.2.2)).trans
      ((B.tests.payload.frame _ _ (row.trans_le beforeChecks.2.1)).trans (B.tests.excess.frame _ _ (row.trans_le beforeChecks.1))),
    (dispatch_exec L rows m ready table signed).2.2 j]; rfl

/-- The kept, discharged and reserved words are read at the same physical row in all branches. -/
theorem stock_at (L : Dispatch) (B : Repair q d) (v : Memory w)
    (plan : AuditReady (audits L B) v) (board : Board L B w)
    (j : Fin L.candidates) (i : Fin d) :
    let r : Word w := j.val
    verdictMemory B.verdict (audits L B) v (B.stockOut i+j.val) = (retained L B i).eval v r ∧
    verdictMemory B.verdict (audits L B) v (B.stockOut i+L.candidates+j.val) = (discharge B i).eval v r ∧
    verdictMemory B.verdict (audits L B) v (B.reserveOut i+j.val) = (saved B i).eval v r := by
  have contains (p : Pass) (hp : p ∈ stockWrites L B i) : p ∈ writes L B := by
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_append_right
    apply List.mem_append_left
    exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i,rfl⟩, hp⟩
  exact ⟨read_at L B v plan board _ (contains _ (List.mem_cons_self ..)) j,
    read_at L B v plan board _ (contains _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) j,
    read_at L B v plan board _ (contains ⟨B.reserveOut i,L.candidates,saved B i⟩ (by simp [stockWrites])) j⟩

theorem stock_read (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w)
    (plan : AuditReady (audits L B) (snapshot L B rows m)) (board : Board L B w)
    (j : Fin L.candidates) (i : Fin d) :
    let v := snapshot L B rows m
    let r : Word w := j.val
    output L B rows m (B.stockOut i+j.val) = (retained L B i).eval v r ∧
    output L B rows m (B.stockOut i+L.candidates+j.val) = (discharge B i).eval v r ∧
    output L B rows m (B.reserveOut i+j.val) = (saved B i).eval v r :=
  stock_at L B (snapshot L B rows m) plan board j i

/-- The control word is computed from the three chronological integer score totals. -/
theorem action_from_sums (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w)
    (plan : AuditReady (audits L B) (snapshot L B rows m)) (board : Board L B w) (j : Fin L.candidates)
    (wide : 0<w) (fits : (AttemptGate.mode B.policy).Fits w B.repairBits.base)
    (stopLo : B.tests.stop.base < B.tests.excess.out)
    (excessLo : B.tests.excess.out+B.tests.excess.rows < B.tests.payload.out)
    (payloadLo : B.tests.payload.out+B.tests.payload.rows < B.tests.discrepancy.out) :
    let u := dispatchMemory L rows m
    output L B rows m (B.modeOut+j.val) =
      (AttemptGate.selectMode B.tests.injection B.tests.reserve (AttemptGate.bit B.tests.stop u)
        (B.tests.excess.high u) (B.tests.payload.high (B.tests.excess.after u))
        (B.tests.discrepancy.high (B.tests.payload.after (B.tests.excess.after u))) : Word w) := by
  rw [action_read L B rows m plan board j, ←AttemptGate.mode_eval B.policy _ (j.val : Word w)]
  exact (eval_below _ _ (tested L B rows m) (snapshot L B rows m) fits
    (fun a ha => ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl ha))).trans
    (B.tests.mode _ _ wide stopLo excessLo payloadLo)

/-- The public half-stock ROM has one small entry per representable stock in this bank. -/
def halfAdvice (bank : Bank) (m : Memory w) : Memory w :=
  fillSegment bank.base bank.size (fun a => (((a-bank.base)/2 : ℕ) : Word w)) m

theorem half_entry (bank : Bank) (m : Memory w) (x : Word w) (fits : x.val < bank.size) :
    bank.read (halfAdvice bank m) x = ((x.val / 2 : ℕ) : Word w) := by
  have inside : bank.base ≤ bank.base+x.val ∧ bank.base+x.val < bank.base+bank.size := by omega
  simp [Bank.read,halfAdvice,fillSegment,Nat.mod_eq_of_lt fits,inside]

/-- A stopped tick writes back both original inventories and no overflow. -/
theorem stopped_stock (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w)
    (plan : AuditReady (audits L B) (snapshot L B rows m)) (board : Board L B w)
    (j : Fin L.candidates) (i : Fin d) (wide : 4≤2^w)
    (stop : AttemptGate.actual B.policy (snapshot L B rows m)=0) :
    let v := snapshot L B rows m
    output L B rows m (B.stockOut i+j.val) = (B.batch.stock i).eval v (j.val:Word w) ∧
    output L B rows m (B.stockOut i+L.candidates+j.val) = 0 ∧
    output L B rows m (B.reserveOut i+j.val) = (B.reserve i).eval v (j.val:Word w) := by
  simpa [retained_eval _ _ _ _ _ wide, discharge_eval _ _ _ _ wide, saved_eval _ _ _ _ wide, stop]
    using stock_read L B rows m plan board j i

/-- A repair writes the actual histogram-updated stock and leaves the reserve and overflow intact. -/
theorem repair_stock (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w)
    (plan : AuditReady (audits L B) (snapshot L B rows m)) (board : Board L B w)
    (j : Fin L.candidates) (i : Fin d) (wide : 4≤2^w)
    (repair : AttemptGate.actual B.policy (snapshot L B rows m)=2) :
    let v := snapshot L B rows m
    let b := enabledBatch L B
    let r : Word w := j.val
    output L B rows m (B.stockOut i+j.val)=(b.nextStock i (b.wire (B.wire i))).eval v r ∧
    output L B rows m (B.stockOut i+L.candidates+j.val)=0 ∧
    output L B rows m (B.reserveOut i+j.val)=(B.reserve i).eval v r := by
  simpa [retained_eval _ _ _ _ _ wide,discharge_eval _ _ _ _ wide,saved_eval _ _ _ _ wide,repair]
    using stock_read L B rows m plan board j i

/-- For each reported repair resource, its emitted width and charged demand balance the
actual stock read before the repair against the stock word retained afterwards. -/
theorem repair_balance (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w)
    (plan : AuditReady (audits L B) (snapshot L B rows m)) (board : Board L B w)
    (j : Fin L.candidates) (i : Fin d) (wide : 4≤2^w)
    (repair : AttemptGate.actual B.policy (snapshot L B rows m)=2) (reports : B.reportWidth=B.wire i)
    (selected : (enabledBatch L B).selected (snapshot L B rows m) (j.val:Word w))
    (valid : (enabledBatch L B).withinPacket (snapshot L B rows m) (j.val:Word w))
    (hist : (∑ k,(((enabledBatch L B).field k).eval (snapshot L B rows m) (j.val:Word w)).val)=B.batch.copies)
    (qFit : q≤2^w) (copiesFit : B.batch.copies<2^w) (sumFit : q*B.batch.copies<2^w)
    (limit : let v := snapshot L B rows m
      let b := enabledBatch L B
      let r : Word w := j.val
      ((b.stock i).eval v r).val-((b.need i).eval v r).val+((b.wire (B.wire i)).eval v r).val<2^w) :
    let v := snapshot L B rows m
    let r : Word w := j.val
    ((B.batch.stock i).eval v r).val+(output L B rows m (B.reportOut 4+j.val)).val =
      (output L B rows m (B.stockOut i+j.val)).val+((B.batch.need i).eval v r).val := by
  let v := snapshot L B rows m
  let b := enabledBatch L B
  let r : Word w := j.val
  have emit : output L B rows m (B.reportOut 4+j.val)=(b.wire (B.wire i)).eval v r := by
    rw [← reports]
    exact (descriptor_read L B rows m plan board j 4).1
  have keeps := (repair_stock L B rows m plan board j i wide repair).1
  have stored := b.nextStock_selected v r i (b.wire (B.wire i)) selected valid hist qFit copiesFit sumFit limit
  have funded : ((b.need i).eval v r).val≤((b.stock i).eval v r).val := selected.2.2 i
  change ((b.stock i).eval v r).val+_ = _+((b.need i).eval v r).val
  rw [emit,keeps,stored]
  omega

/-- The initial purchase splits the *actual* stock by integer division before any feed,
without installing a positive width or debiting a histogram replacement. -/
theorem split_stock (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w)
    (plan : AuditReady (audits L B) (snapshot L B rows m)) (board : Board L B w)
    (j : Fin L.candidates) (i : Fin d) (wide : 4≤2^w)
    (buy : AttemptGate.actual B.policy (snapshot L B rows m)=3)
    (half : let x := (B.batch.stock i).eval (snapshot L B rows m) (j.val:Word w)
      B.halfTable.read (snapshot L B rows m) x = ((x.val/2 : ℕ):Word w)) :
    let old := ((B.batch.stock i).eval (snapshot L B rows m) (j.val:Word w)).val
    (output L B rows m (B.stockOut i+j.val)).val = old/2 ∧
    output L B rows m (B.stockOut i+L.candidates+j.val) = 0 ∧
    (output L B rows m (B.reserveOut i+j.val)).val = old-old/2 := by
  let v := snapshot L B rows m
  let x := (B.batch.stock i).eval v (j.val:Word w)
  have hlt : x.val/2 < 2^w := (Nat.div_le_self ..).trans_lt x.isLt
  have hhalf : (B.halfTable.read v x).val = x.val/2 :=
    (congrArg Fin.val half).trans (Fin.val_cast_of_lt hlt)
  have le : B.halfTable.read v x ≤ x := Fin.le_def.mpr (hhalf.trans_le (Nat.div_le_self ..))
  obtain ⟨keep,overflow,save⟩ := stock_read L B rows m plan board j i
  simp [retained_eval _ _ _ _ _ wide, discharge_eval _ _ _ _ wide, saved_eval _ _ _ _ wide, buy] at keep overflow save
  exact ⟨(congrArg Fin.val keep).trans hhalf,overflow,
    (congrArg Fin.val save).trans (by rw [Fin.sub_val_of_le le,hhalf])⟩

/-- At a scheduled feed tick the integer reserve slice is added to every live stock,
then capped and charged as overflow. No histogram decision is needed for this feed. -/
theorem advance_stock (L : Dispatch) (B : Repair q d)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (m : Memory w)
    (plan : AuditReady (audits L B) (snapshot L B rows m)) (board : Board L B w)
    (j : Fin L.candidates) (i : Fin d) (wide : 4≤2^w)
    (advance : AttemptGate.actual B.policy (snapshot L B rows m)=1) (feedTick : B.feedOnAdvance=true)
    (capFit : B.cap i < 2^w) (steps bits old : ℕ)
    (reserveWord : (B.reserve i).eval (snapshot L B rows m) (j.val:Word w) = (bits:Word w))
    (stockWord : (B.batch.stock i).eval (snapshot L B rows m) (j.val:Word w) = (old:Word w))
    (entry : B.feedTable.read (snapshot L B rows m) ((B.mesh*B.feedStride+bits:ℕ):Word w) =
      (AdaptiveProbe.slice steps bits B.mesh:Word w)) (fits : old+AdaptiveProbe.slice steps bits B.mesh < 2^w) :
    let total := old+AdaptiveProbe.slice steps bits B.mesh
    (output L B rows m (B.stockOut i+j.val)).val = min total (B.cap i) ∧
    (output L B rows m (B.stockOut i+L.candidates+j.val)).val = total-min total (B.cap i) := by
  let v := snapshot L B rows m
  let r : Word w := j.val
  have actual : ((fedStock B i).eval v r).val = old+AdaptiveProbe.slice steps bits B.mesh :=
    (congrArg Fin.val (feed_readback B.feedTable B.feedStride steps B.mesh bits old
      (B.reserve i) (B.batch.stock i) v r reserveWord stockWord entry)).trans (Fin.val_cast_of_lt fits)
  obtain ⟨keep,overflow,_⟩ := stock_read L B rows m plan board j i
  simp [retained_eval _ _ _ _ _ wide, discharge_eval _ _ _ _ wide, advance, feedTick] at keep overflow
  rw [keep,overflow]
  exact ⟨(StockAccounts.clipped_word (B.cap i) (fedStock B i) v r capFit).trans (by rw [actual]),
    (StockAccounts.overflow_word (B.cap i) (fedStock B i) v r capFit).trans (by rw [actual])⟩

/-- The frozen-stratum producer exposes its union in one ordinary row bank. Other
parts of a full dispatch layout are unused by the postprocessing interpreter. -/
def postLayout (flags rows : ℕ) : Dispatch :=
  ⟨rows,0,0,0,0,flags-4,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩

theorem decisionBase_postLayout (flags rows : ℕ) (room : 4≤flags) :
    decisionBase (postLayout flags rows)=flags := by
  simp [decisionBase,postLayout]; omega

/-- One shared decision and stock split after the complete union of signed strata was
computed from the frozen old stock. The first argument of `postOutput` is that memory. -/
def postFrozen (w : ℕ) (L : Dispatch) (B : Repair q d) : Procedure w :=
  (B.tests.code w).seq ((scan w B.repairBits.base L.candidates (repairMask B)).seq
    (finalVerdict w B.verdict (audits L B)))

def postSnapshot (L : Dispatch) (B : Repair q d) (m : Memory w) :=
  image B.repairBits.base L.candidates (repairMask B) (B.tests.after m)

noncomputable def postOutput (L : Dispatch) (B : Repair q d) (m : Memory w) :=
  verdictMemory B.verdict (audits L B) (postSnapshot L B m)

def postTicks (L : Dispatch) (B : Repair q d) :=
  B.tests.ticks + ((4+L.candidates*(2*(repairMask B).work+4)) +
    (auditTicks (audits L B)+(4+1*(2*(verdict (audits L B)).work+4))))

attribute [local irreducible] CheapCode in
theorem postFrozen_cheap (w : ℕ) (L : Dispatch) (B : Repair q d) : CheapCode (postFrozen w L B) :=
  cheap_seq (A:=B.tests.code w) (B:=(scan w B.repairBits.base L.candidates (repairMask B)).seq (finalVerdict w B.verdict (audits L B))) (B.tests.cheap w) (cheap_seq (A:=scan w B.repairBits.base L.candidates (repairMask B)) (B:=finalVerdict w B.verdict (audits L B))
    (scan_cheap w B.repairBits.base L.candidates (repairMask B)) (finalVerdict_cheap w B.verdict (audits L B)))

theorem postFrozen_exec (L : Dispatch) (B : Repair q d) (m : Memory w) (wide : 0<w)
    (tests : TestsReady B m) (enableFits : (repairMask B).Fits w B.repairBits.base)
    (enableRoom : B.repairBits.base+L.candidates<2^w)
    (plan : AuditReady (audits L B) (postSnapshot L B m)) (order : OrderedTallies (audits L B))
    (deps : (verdict (audits L B)).Fits w B.verdict) (space : B.verdict+1<2^w) :
    (postFrozen w L B).Exec m (postOutput L B m) (postTicks L B) ∧
    (postOutput L B m B.verdict=0 ↔ ∀ j<L.candidates,(enabledBatch L B).valid (postSnapshot L B m) (j:Word w)) := by
  refine ⟨Procedure.Exec.then (A:=B.tests.code w) (B.tests.exec m tests.1 tests.2.1 tests.2.2)
    (Procedure.Exec.then (A:=scan w B.repairBits.base L.candidates (repairMask B)) (B:=finalVerdict w B.verdict (audits L B))
      (scan_exec B.repairBits.base L.candidates (repairMask B) (B.tests.after m) enableFits enableRoom)
      (finalVerdict_exec (audits L B) B.verdict _ plan deps space)), ?_⟩
  exact (finalVerdict_flag (audits L B) B.verdict _ plan order wide).trans
    ⟨fun h => h.1,fun h => ⟨h,admitted_columns _ _⟩⟩

theorem post_read (L : Dispatch) (B : Repair q d) (m : Memory w)
    (plan : AuditReady (audits L B) (postSnapshot L B m)) (board : Board L B w)
    (p : Pass) (hp : p∈writes L B) (j : Fin p.rows) :
    postOutput L B m (p.out+j.val)=p.term.eval (postSnapshot L B m) (j.val:Word w) :=
  read_at L B (postSnapshot L B m) plan board p hp j

theorem post_stock_read (L : Dispatch) (B : Repair q d) (m : Memory w)
    (plan : AuditReady (audits L B) (postSnapshot L B m)) (board : Board L B w) (j : Fin L.candidates) (i : Fin d) :
    let v := postSnapshot L B m
    let r : Word w := j.val
    postOutput L B m (B.stockOut i+j.val)=(retained L B i).eval v r ∧
    postOutput L B m (B.stockOut i+L.candidates+j.val)=(discharge B i).eval v r ∧
    postOutput L B m (B.reserveOut i+j.val)=(saved B i).eval v r :=
  stock_at L B (postSnapshot L B m) plan board j i

/-- Price, commodity and register expressions below the output area have identical
values in the masked snapshot and in the memory consumed by the later sparse commit. -/
theorem post_input (L : Dispatch) (B : Repair q d) (m : Memory w) (t : Expr) (r : Word w) (cut : ℕ)
    (plan : AuditReady (audits L B) (postSnapshot L B m)) (fits : t.Fits w cut)
    (checks : ∀ a∈audits L B, cut≤a.low) (endFlag : cut≤B.verdict) :
    t.eval (postOutput L B m) r=t.eval (postSnapshot L B m) r := by
  apply eval_below _ _ _ _ fits
  intro x hx
  change image B.verdict 1 _ (auditOut (audits L B) (postSnapshot L B m)) x=_
  rw [ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (hx.trans_le endFlag))]
  exact audit_below _ _ plan x (fun a ha => hx.trans_le (checks a ha))

theorem post_selected (L : Dispatch) (B : Repair q d) (m : Memory w) (j : Fin L.candidates)
    (width : 4≤2^w) (room : L.candidates≤2^w) (padded : L.candidates≤B.repairBits.size) :
    let v := postSnapshot L B m
    let tested := B.tests.after m
    let r : Word w := j.val
    (enabledBatch L B).selected v r ↔ (AttemptGate.actual B.policy tested=2 ∧
      B.failedMIS.read tested (B.batch.owner.eval tested r)≠0) ∧ B.batch.packet.eval v r≠0 ∧
      ∀ i,((B.batch.need i).eval v r).val≤((B.batch.stock i).eval v r).val := by
  change B.repairBits.read (postSnapshot L B m) (j.val:Word w)≠0 ∧ _ ∧ _ ↔ _
  rw [Bank.read,Fin.val_cast_of_lt (j.isLt.trans_le room),Nat.mod_eq_of_lt (j.isLt.trans_le padded)]
  rw [show postSnapshot L B m (B.repairBits.base+j.val)=(repairMask B).eval (B.tests.after m) (j.val:Word w) from
    ProtocolRAMGeneratedWrite.read_image ..]
  simp only [repairMask,AttemptGate.ifRepair,AttemptGate.ifMode_eval _ _ _ _ _ _ width (by decide : 2<4),Expr.eval]
  split_ifs <;> simp_all [enabledBatch,Batch.need,Batch.packet]

theorem post_flag (L : Dispatch) (B : Repair q d) (m : Memory w)
    (plan : AuditReady (audits L B) (postSnapshot L B m)) (board : Board L B w)
    (wide : 4≤2^w) (fits : decisionBase L+L.candidates≤2^w)
    (padded : L.candidates≤2^B.decisionBits) (j : Fin L.candidates)
    (tests : decisionBase L+L.candidates≤B.tests.excess.out ∧ decisionBase L+L.candidates≤B.tests.payload.out ∧
      decisionBase L+L.candidates≤B.tests.discrepancy.out)
    (sep : decisionBase L+L.candidates≤B.repairBits.base) :
    postOutput L B m (B.purchaseOut+j.val) = if AttemptGate.actual B.policy (postSnapshot L B m)=3
      then m (decisionBase L+j.val) else 0 := by
  rw [post_read L B m plan board ⟨_,L.candidates,buyWord L B⟩ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) j]
  have h := j.isLt
  simp only [buyWord,AttemptGate.ifPurchase,AttemptGate.ifMode_eval _ _ _ _ _ _ wide (by decide : 3<4),
    Expr.eval,Bank.read,Bank.size,Fin.val_cast_of_lt (show j.val<2^w by omega),Nat.mod_eq_of_lt (h.trans_le padded)]
  have low := Nat.add_lt_add_left h (decisionBase L)
  have keep : postSnapshot L B m (decisionBase L+j.val)=m (decisionBase L+j.val) := by
    rw [postSnapshot,ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (low.trans_le sep)),
      AttemptGate.TestBoard.after,B.tests.discrepancy.frame _ _ (low.trans_le tests.2.2),
      B.tests.payload.frame _ _ (low.trans_le tests.2.1),B.tests.excess.frame _ _ (low.trans_le tests.1)]
  rw [keep]
  simp

end Hierarchy.ProtocolRAM.PurchaseStage

end OAI

import OAI.Hierarchy.ProtocolRAMNativePriceLabels
import OAI.Hierarchy.ProtocolRAMStockStageFrame
import OAI.Hierarchy.ProtocolRAMCalendarCommitLayout
import OAI.Hierarchy.ProtocolRAMRouteSettlement
import OAI.Hierarchy.ProbeBudget

namespace OAI
/-! # Native chronological charge labels taken from the reported physical edge geometry -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {w q d edges : ℕ}

theorem LabelSource.resolve_port (out commonBase : ℕ) (geometry : Fin 7 → Expr) (role : Expr) (common : Fin d → Expr)
    (m : Memory w) (r : Word w) (i : Fin d) (e : Fin edges) (fits : d≤2^w)
    (which : (role.eval m r).val=i.val) (id : (common i).eval m r=((commonBase+e.val:ℕ):Word w)) :
    (LabelSource.fromPorts out commonBase geometry role common).edge.eval m r=(e.val:Word w) := by
  change ((chooseField d 0 common role).eval m r - (commonBase:Word w))=(e.val:Word w)
  rw [eval_chooseField _ _ _ _ _ _ i (by simpa using fits) (by simpa using which),id,Nat.cast_add]
  abel

theorem LabelSource.read (g : LabelSource) (n : ℕ) (m : Memory w) (e : Fin n) :
    (g.pass n).apply m (g.out+e.val)=(g.geometry 5).eval m (g.edge.eval m (e.val:Word w)) := by
  rw [show (g.pass n).apply m (g.out+e.val)=((g.geometry 5).atRow g.edge).eval m (e.val:Word w) from
    ProtocolRAMGeneratedWrite.read_image ..,eval_atRow]

theorem pricedTicks (a : Area) (s : Sources) (g : LabelSource) (w : ℕ) (b : Batch q d) :
    (pricedSegment a s g w b).ticks=4+a.occurrences*(2*((g.geometry 5).atRow g.edge).work+4)+
      (4+18*a.goods+((fresh a s).native w a.rows b).ticks) := by
  change _+(freshSegment a s w b).ticks=_
  rw [freshSegment_ticks]
  rfl

theorem pricedSize (a : Area) (s : Sources) (g : LabelSource) (w : ℕ) (b : Batch q d) :
    let p := (pricedSegment a s g w b).native
    let base := (freshSegment a s w b).native
    let term := (g.geometry 5).atRow g.edge
    p.labels=(7+3*term.work)+base.labels ∧ p.registers=(4+term.work)+base.registers ∧ p.slots=base.slots := by
  dsimp only
  change ((6+(((g.geometry 5).atRow g.edge).compile w g.out).labels)+_=_ ∧
    (4+(((g.geometry 5).atRow g.edge).compile w g.out).binds)+_=_ ∧ 0+_=_)
  simp only [DescriptorExpr.Term.labels_eq,compile_binds,Nat.zero_add,and_self, and_true]
  omega

set_option maxHeartbeats 800000 in
theorem price_label (a : Area) (s : Sources) (g : LabelSource) (b : Batch q d) (m : Memory w) (e : Fin a.occurrences)
    (mounted : (pricedSegment a s g w b).ready m) (before : g.out+a.occurrences≤a.start) :
    (pricedSegment a s g w b).after m (g.out+e.val)=(g.geometry 5).eval m (g.edge.eval m (e.val:Word w)) := by
  let entry := (g.pass a.occurrences).apply m
  have ready : (freshSegment a s w b).ready entry := mounted.2
  have early : g.out+e.val<a.start := (Nat.add_lt_add_left e.isLt _).trans_le before
  have fixed := (freshSegment a s w b).frame entry (g.out+e.val) ready
    (fresh_keeps a s b (g.out+e.val) (Or.inl early))
  exact fixed.trans (g.read a.occurrences m e)

/-- A pricing segment only requires the public source geometry and immutable ordinal
banks. Its memory safety holds on malformed packet and edge words as well. -/
theorem pricedSegment_ready (a : Area) (s : Sources) (g : LabelSource) (b : Batch q d) (m : Memory w)
    (h : PrefixFits a s b) (fit : ((g.geometry 5).atRow g.edge).inputEnd≤g.out)
    (before : g.out+a.occurrences≤a.start) (oldOwner : s.owner.base+s.owner.size≤g.out)
    (oldParity : s.parity.base+s.parity.size≤g.out) (room : a.stop<2^w)
    (dir : RepairHistogram.PairDirectory (a.columns s) m a.occurrences) : (pricedSegment a s g w b).ready m := by
  obtain ⟨goods,seed,fees,flags,tape,cap,capOut,last⟩ := a.order
  have same (bank : Bank) (hBank : bank.base+bank.size≤g.out) (r : Word w) :
      bank.read ((g.pass a.occurrences).apply m) r=bank.read m r := by
    have small := Nat.mod_lt r.val (Nat.two_pow_pos bank.bits)
    change r.val%bank.size<bank.size at small
    exact ProtocolRAMGeneratedWrite.frame_image g.out a.occurrences ((g.geometry 5).atRow g.edge) m _ (.inl (by omega))
  exact ⟨(g.pass a.occurrences).fits_of_span fit (by change g.out+a.occurrences<2^w;omega),
    freshSegment_ready a s b _ h room
      ⟨fun e => (same s.parity oldParity _).trans (dir.first e),fun e => (same s.parity oldParity _).trans_ne (dir.second e),
       fun e => (same s.owner oldOwner _).trans (dir.firstRow e),fun e => (same s.owner oldOwner _).trans (dir.secondRow e)⟩⟩

theorem stock_origin (a : Area) (s : Sources) (g : LabelSource) (m : Memory w) (i : Fin a.goods)
    (width : a.goods≤2^w) (size : a.goods≤ s.old.size) (below : s.old.base+s.old.size≤g.out) :
    stageInput a s g m (a.start+i.val)=m (s.old.base+i.val) :=
  (a.seed_read s _ i width size).trans (ProtocolRAMGeneratedWrite.frame_image g.out a.occurrences ((g.geometry 5).atRow g.edge) m _ (.inl (by have := i.isLt;omega)))

theorem stage_input (a : Area) (s : Sources) (g : LabelSource) (m : Memory w) (e : Expr) (r : Word w)
    (fit : e.Fits w g.out) (before : g.out≤a.start) : e.eval (stageInput a s g m) r=e.eval m r := by
  apply eval_below _ _ _ _ fit
  intro x hx
  exact (a.seed_frame s _ x (.inl (hx.trans_le before))).trans (ProtocolRAMGeneratedWrite.frame_image g.out a.occurrences ((g.geometry 5).atRow g.edge) m _ (.inl hx))

/-- Labels used by the signed account. An ordinary toll reads `lengthCode`; selector
broadcast reads its committed menu, and a bought capacity reads its own link length.
Route and phase rates that are public constants may ignore their emitted label. -/
def reportedKeys (a : Area) (g : LabelSource) (B : PurchaseStage.Repair q d) (routeKey : Fin a.goods → ℕ) :
    RepairHistogram.CashKeys a.occurrences a.rows a.goods a.rows :=
  ⟨fun e=>g.out+e.val,fun j=>B.reportOut 6+j.val,routeKey,fun j=>B.boughtFields 5+j.val⟩

def lengthPrice (den : ℝ) (code : ℕ) := (code:ℝ)/den

def externalPrice (supply : Bool) (M den : ℝ) (code : ℕ) := if supply then 2*M else lengthPrice den code

def boughtPrice (Λ p q Q t den : ℝ) (code : ℕ) := Λ*capacity p q Q t (lengthPrice den code)

theorem boughtPrice_unit (Λ p q Q t den : ℝ) (code : ℕ) (unit : lengthPrice den code=1) (on : t≠0) :
    boughtPrice Λ p q Q t den code=Λ*t^p := by simp [boughtPrice,capacity,unit,on]

theorem boughtPrice_off (Λ p q Q den : ℝ) (code : ℕ) : boughtPrice Λ p q Q 0 den code=0 := by
  simp [boughtPrice,capacity]

/-- A padded catalogue has fee zero on an unopened row for every code in memory. -/
theorem chosen_capacity (Λ p q Q t den : ℝ) (code : ℕ) (picked : Bool) :
    (if picked then boughtPrice Λ p q Q t den code else 0)=boughtPrice Λ p q Q (if picked then t else 0) den code := by
  cases picked <;> simp [boughtPrice_off]

/-- Coordinates may vary with the earlier matching. Evaluating the physical edge
expression at this occurrence identifies the exact final settled row, including
when several charged occurrences contribute to the same final edge. -/
theorem reported_length {I C : Type*} [Fintype I] [Fintype C] {r : ℕ}
    {core : I → List (Fin edges)} {center : C → List (Fin edges)} (a : Area) (s : Sources) (g : LabelSource)
    (b : Batch q d) (m terminal : Memory w) (e : Fin a.occurrences) (j : Fin edges)
    (mounted : (pricedSegment a s g w b).ready m) (order : g.out+a.occurrences≤a.start)
    (resolve : g.edge.eval m (e.val:Word w)=(j.val:Word w)) (banks : RouteSettlement.Banks) (src : ℕ)
    (enum : Fin r ≃ RouteOccurrence core center) (ci : I → ℕ) (cj : C → ℕ)
    (cut : ℕ) (fit : (g.geometry 5).Fits w cut) (before : cut≤banks.width.base) (space : banks.width.base+edges≤ src)
    (history : ∀ x<cut,terminal x=m x) :
    (((pricedSegment a s g w b).after m) (g.out+e.val)).val =
      (reportedRows [] (RouteSettlement.fields banks g.geometry) (RouteSettlement.output banks src terminal enum ci cj) j).lengthCode := by
  rw [price_label a s g b m e mounted order,resolve]
  change _ = (reportedRows [] (RouteSettlement.fields banks g.geometry) (RouteSettlement.output banks src terminal enum ci cj) j).field 5
  rw [RouteSettlement.geometry_read banks src terminal enum ci cj g.geometry j 5 (by decide)
    (ProtocolRAMGeneratedWrite.fits_mono _ before fit) space]
  exact congrArg Fin.val (eval_below _ _ m terminal fit history).symm

theorem post_descriptor (L : PurchaseStage.Dispatch) (B : PurchaseStage.Repair q d) (m : Memory w)
    (plan : AuditReady (PurchaseStage.audits L B) (PurchaseStage.postSnapshot L B m)) (board : PurchaseStage.Board L B w)
    (j : Fin L.candidates) (k : Fin 7) :
    let out := PurchaseStage.postOutput L B m
    let snap := PurchaseStage.postSnapshot L B m
    out (B.reportOut k+j.val)=(B.link.fields (PurchaseStage.enabledBatch L B) B.reportWidth k).eval snap (j.val:Word w) ∧
    out (B.boughtFields k+j.val)=(PurchaseStage.buyFields L B k).eval snap (j.val:Word w) := by
  constructor <;> apply PurchaseStage.post_read L B m plan board ⟨_,L.candidates,_⟩ _ j
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

/-- Physical tags behind both the broadcast and the purchased length. The printed
purchase menu is observed as well, using its original seventh field. -/
theorem post_keys (L : PurchaseStage.Dispatch) (B : PurchaseStage.Repair q d) (m : Memory w)
    (plan : AuditReady (PurchaseStage.audits L B) (PurchaseStage.postSnapshot L B m)) (board : PurchaseStage.Board L B w)
    (qFit : q≤2^w) (copyFit : B.batch.copies<2^w) (sumFit : q*B.batch.copies<2^w) (j : Fin L.candidates) :
    let b := PurchaseStage.enabledBatch L B
    let out := PurchaseStage.postOutput L B m
    let snap := PurchaseStage.postSnapshot L B m
    let r : Word w := j.val
    out (B.reportOut 6+j.val)=(if RepairHistogram.committed b snap r then b.packet.eval snap r else 0) ∧
    out (B.boughtFields 5+j.val)=B.purchaseLink.lengthCode.eval snap r ∧
    out (B.boughtFields 6+j.val)=(if (PurchaseStage.buyWord L B).eval snap r=0 then 0 else B.purchaseMenu.eval snap r) := by
  let b := PurchaseStage.enabledBatch L B
  let snap := PurchaseStage.postSnapshot L B m
  let r : Word w := j.val
  refine ⟨(post_descriptor L B m plan board j 6).1.trans ?_,(post_descriptor L B m plan board j 5).2,
    (post_descriptor L B m plan board j 6).2.trans ?_⟩
  · change (b.ifSelected (b.ifPacket b.packet (.lit 0)) (.lit 0)).eval snap r=
      (if RepairHistogram.committed b snap r then b.packet.eval snap r else 0)
    rw [b.eval_ifSelected,b.eval_ifPacket snap r _ _ qFit copyFit sumFit]
    by_cases selected : b.selected snap r <;> simp [RepairHistogram.committed,selected,Expr.eval]
  · change (Expr.branch .eq (PurchaseStage.buyWord L B) (.lit 0) (.lit 0) B.purchaseMenu).eval snap r=
      (if (PurchaseStage.buyWord L B).eval snap r=0 then 0 else B.purchaseMenu.eval snap r)
    simp [Expr.eval,Comparison.test,beq_iff_eq]

theorem priced_stamps (a : Area) (s : Sources) (g : LabelSource) (L : PurchaseStage.Dispatch) (B : PurchaseStage.Repair q d)
    (m : Memory w) (j : Fin L.candidates) (plan : AuditReady (PurchaseStage.audits L B) (PurchaseStage.postSnapshot L B m))
    (board : PurchaseStage.Board L B w) (qFit : q≤2^w) (copyFit : B.batch.copies<2^w) (sumFit : q*B.batch.copies<2^w)
    (mounted : (pricedSegment a s g w (PurchaseStage.enabledBatch L B)).ready (PurchaseStage.postOutput L B m))
    (order : g.out+a.occurrences≤a.start) (menu : B.reportOut 6+j.val<g.out)
    (length : B.boughtFields 5+j.val<g.out) (buyMenu : B.boughtFields 6+j.val<g.out) :
    let b := PurchaseStage.enabledBatch L B
    let out := (pricedSegment a s g w b).after (PurchaseStage.postOutput L B m)
    let snap := PurchaseStage.postSnapshot L B m
    let r : Word w := j.val
    out (B.reportOut 6+j.val)=(if RepairHistogram.committed b snap r then b.packet.eval snap r else 0) ∧
    out (B.boughtFields 5+j.val)=B.purchaseLink.lengthCode.eval snap r ∧
    out (B.boughtFields 6+j.val)=(if (PurchaseStage.buyWord L B).eval snap r=0 then 0 else B.purchaseMenu.eval snap r) := by
  let b := PurchaseStage.enabledBatch L B
  have prior (x : ℕ) (hx : x<g.out) := (pricedSegment a s g w b).frame (PurchaseStage.postOutput L B m) x mounted
    (priced_keeps a s g b x order (.inl hx))
  obtain ⟨first,second,third⟩ := post_keys L B m plan board qFit copyFit sumFit j
  exact ⟨(prior _ menu).trans first,(prior _ length).trans second,(prior _ buyMenu).trans third⟩

/-- The printed link-ID of an acquisition belongs to the candidate's original
ordinal. Equal endpoints in different rows do not merge their IDs. -/
theorem buy_id (a : Area) (s : Sources) (g : LabelSource) (L : PurchaseStage.Dispatch) (B : PurchaseStage.Repair q d)
    (m : Memory w) (j : Fin L.candidates) (plan : AuditReady (PurchaseStage.audits L B) (PurchaseStage.postSnapshot L B m))
    (board : PurchaseStage.Board L B w)
    (mounted : (pricedSegment a s g w (PurchaseStage.enabledBatch L B)).ready (PurchaseStage.postOutput L B m))
    (order : g.out+a.occurrences≤a.start) (earlier : B.boughtFields 3+j.val<g.out)
    (room : B.purchaseLink.idBase+L.candidates≤2^w) :
    let b := PurchaseStage.enabledBatch L B
    let out := (pricedSegment a s g w b).after (PurchaseStage.postOutput L B m)
    (out (B.boughtFields 3+j.val)).val=B.purchaseLink.idBase+j.val := by
  dsimp only
  have stamp := (pricedSegment a s g w (PurchaseStage.enabledBatch L B)).frame _ _ mounted
    (priced_keeps a s g _ _ order (.inl earlier))
  rw [stamp,(post_descriptor L B m plan board j 3).2]
  change ((B.purchaseLink.idBase:Word w)+(j.val:Word w)).val=B.purchaseLink.idBase+j.val
  rw [←Nat.cast_add,Fin.val_cast_of_lt (by have := j.isLt;omega)]

/-- Prepaid capacity is charged exactly once per candidate ID, including zero-width
opened rows. An unopened public placeholder contributes at scale zero. -/
theorem opened_fee_sum {n : ℕ} (m : Memory w) (flag key : Fin n → ℕ) (Λ p q Q den : ℝ) (time : Fin n → ℝ)
    (bit : ∀ j,(m (flag j)).val≤1) :
    (∑ j : Fin n,((m (flag j)).val:ℝ)*boughtPrice Λ p q Q (time j) den (m (key j)).val)=
      Λ*∑ j : Fin n,capacity p q Q (if (m (flag j)).val=0 then 0 else time j) (lengthPrice den (m (key j)).val) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rcases (show (m (flag j)).val=0 ∨ (m (flag j)).val=1 by have := bit j;omega) with h|h
  · simp [h,capacity]
  · simp [h,boughtPrice]

end
end Hierarchy.ProtocolRAM.Calendar.StockCommit

end OAI

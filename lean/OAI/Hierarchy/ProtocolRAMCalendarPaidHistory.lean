import OAI.Hierarchy.ProtocolRAMCalendarCash
import OAI.Hierarchy.ProtocolRAMCalendarArena

namespace OAI
/-! # A concrete cumulative index for historical signed charge words -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section

/-- Block `j` contains exactly the physical charge outputs of the event at
position `j`. Historical payments are represented by their immutable words
in their original positions. -/
structure PriceHistory where
  count : ℕ→ℕ
  emit : (j : ℕ)→Fin (count j)→ChargeWord

def PriceHistory.size (P : PriceHistory) : ℕ→ℕ
  | 0 => 0
  | j+1 => P.size j+P.count j

def PriceHistory.word (P : PriceHistory) : (j : ℕ)→Fin (P.size j)→ChargeWord
  | 0 => Fin.elim0
  | j+1 => Fin.addCases (P.word j) (P.emit j)

def cursor (c : Mesh) (a : Attempt) := position c (.attempt a)

/-- Every historical inventory view reads the complete charge prefix ending at
its physical cursor. No stored cumulative sum or real-valued arithmetic
instruction is needed. -/
def PriceHistory.account {I : Type*} (P : PriceHistory) (c : Mesh) (model : AccountColumns I) : AccountColumns I :=
  {model with
    charges:=fun a=>P.size (cursor c a)
    widthAt:=fun a i=>(P.word (cursor c a) i).width
    priceKeyAt:=fun a i=>(P.word (cursor c a) i).key
    unitPrice:=fun a i=>(P.word (cursor c a) i).price}

theorem PriceHistory.row {I : Type*} (P : PriceHistory) (c : Mesh) (model : AccountColumns I)
    (a : Attempt) (i : Fin (P.size (cursor c a))) : (P.account c model).row a i=P.word (cursor c a) i := by
  rfl

private theorem position_outer_next (c : Mesh) (p h : ℕ) :
    cursor c (.inner p h 0 0)=cursor c (.outer p h)+1 := by simp [cursor,position,sliceBase]

private theorem position_inner_next (c : Mesh) (p h j b : ℕ) :
    cursor c (.inner p h j (b+1))=cursor c (.inner p h j b)+1 := by simp [cursor,position,Nat.add_assoc]

private theorem position_feed_inner (c : Mesh) (p h j : ℕ) :
    cursor c (.inner p h (j+1) 0)=cursor c (.inner p h j c.innerFuel)+1 := by
  simp [cursor,position,sliceBase,sliceSize,Nat.succ_mul]; omega

private theorem position_feed_outer (c : Mesh) (p : ℕ) :
    cursor c (.outer (p+1) 0)=cursor c (.outer p c.outerFuel)+1 := by
  simp [cursor,position,trialBase,Nat.succ_mul,phaseSize]; omega

theorem position_trial_end (c : Mesh) (p h : ℕ) :
    cursor c (.outer p (h+1))=cursor c (.inner p h c.reserveSteps 0) := by
  simp [cursor,position,trialBase,sliceBase,trialSize,Nat.succ_mul]; omega

/-- Chronological aliasing of historical costs at the end of a reserve replay.
The two inventory views select the next live stock bank at the same addresses. -/
theorem PriceHistory.alias {I : Type*} (P : PriceHistory) (c : Mesh) (model : AccountColumns I)
    (a b : Attempt) (pos : cursor c a=cursor c b) (stock : model.stockAt a=model.stockAt b)
    {w : ℕ} (m : Memory w) : (P.account c model).read a m=(P.account c model).read b m := by
  let paidAt (j : ℕ) := model.initialCharge +
    (∑ r : Fin (P.size j), ((m (P.word j r).width).val : ℝ) *
      (P.word j r).price (m (P.word j r).key).val) / model.payloadWidth
  change Inventory.mk (fun i => (m (model.stockAt a i)).val) (paidAt (cursor c a)) =
    Inventory.mk (fun i => (m (model.stockAt b i)).val) (paidAt (cursor c b))
  rw [stock, pos]

/-- Every charge in the prefix was actually emitted by a strictly earlier event. -/
theorem PriceHistory.source (P : PriceHistory) (j : ℕ) (i : Fin (P.size j)) :
    ∃ t<j, ∃ k : Fin (P.count t),P.word j i=P.emit t k := by
  induction j with
  | zero => exact Fin.elim0 i
  | succ j ih =>
    refine Fin.addCases (fun l=>?_) (fun r=>?_) i
    · obtain ⟨t,ht,k,hk⟩ := ih l
      exact ⟨t,Nat.lt_succ_of_lt ht,k,by simpa only [word,Fin.addCases_left] using hk⟩
    · exact ⟨j,Nat.lt_succ_self _,r,by simp [word]⟩

/-- The matching equivalence in the chronological cash-append theorem is forced by
the contiguous two intervals. The previous count may be zero. -/
def PriceHistory.extend (P : PriceHistory) (j : ℕ) :
    Fin (P.size j) ⊕ Fin (P.count j) ≃ Fin (P.size (j+1)) := finSumFinEquiv

theorem PriceHistory.old_row (P : PriceHistory) (j : ℕ) (i : Fin (P.size j)) :
    P.word (j+1) (P.extend j (.inl i))=P.word j i :=
  @Fin.addCases_left (P.size j) (P.count j) (fun _ => ChargeWord) (P.word j) (P.emit j) i

theorem PriceHistory.new_row (P : PriceHistory) (j : ℕ) (i : Fin (P.count j)) :
    P.word (j+1) (P.extend j (.inr i))=P.emit j i :=
  @Fin.addCases_right (P.size j) (P.count j) (fun _ => ChargeWord) (P.word j) (P.emit j) i

theorem PriceHistory.word_cast (P : PriceHistory) {j t : ℕ} (eq : j = t)
    (i : Fin (P.size j)) : P.word t (Fin.cast (congrArg P.size eq) i) = P.word j i := by
  subst t
  rfl

/-- No cost estimate is assumed: the cumulative balance is obtained by appending
this event's actual indexed payments and preserving both words of every prefix row. -/
theorem PriceHistory.post {I : Type*} (P : PriceHistory) (model : AccountColumns I)
    {w q d : ℕ} (C : Chart w q d) (a b : Attempt) (e : Event) (m : Memory w)
    (next : cursor C.mesh b=cursor C.mesh a+1) (step : ready C e m)
    (safe : ∀i, let r := P.word (cursor C.mesh a) i
      protected C r.width e ∧ protected C r.key e) :
    let A := P.account C.mesh model
    let out := after C e m
    (A.read b out).paid=(A.read a m).paid+
      ∑i,(P.emit (cursor C.mesh a) i).value A.payloadWidth out := by
  intro A out
  let idx := cursor C.mesh a
  let e' : Fin (P.size idx) ⊕ Fin (P.count idx) ≃ Fin (P.size (cursor C.mesh b)) :=
    (P.extend idx).trans (finCongr (congrArg P.size next.symm))
  apply A.append_executed C [e] m a b (P.emit idx) e'
  · intro i
    change P.word (cursor C.mesh b) (e' (.inl i))=P.word idx i
    exact (P.word_cast next.symm _).trans (P.old_row idx i)
  · intro i
    change P.word (cursor C.mesh b) (e' (.inr i))=P.emit idx i
    exact (P.word_cast next.symm _).trans (P.new_row idx i)
  · exact ⟨step,trivial⟩
  · intro i e' membership
    obtain rfl := List.mem_singleton.mp membership
    exact safe i

def Succession (c : Mesh) (e : Event) : Attempt × Attempt :=
  match e with
  | .attempt (.outer p h) => (.outer p h,.inner p h 0 0)
  | .attempt (.inner p h j b) => (.inner p h j b,.inner p h j (b+1))
  | .feed (.inner p h j) => (.inner p h j c.innerFuel,.inner p h (j+1) 0)
  | .feed (.outer p) => (.outer p c.outerFuel,.outer (p+1) 0)

theorem Succession.next (c : Mesh) (e : Event) :
    cursor c (Succession c e).2=cursor c (Succession c e).1+1 := by
  rcases e with (⟨p,h⟩|⟨p,h,j,b⟩) | (⟨p⟩|⟨p,h,j⟩)
  · exact position_outer_next c p h
  · exact position_inner_next c p h j b
  · exact position_feed_outer c p
  · exact position_feed_inner c p h j

/-- It suffices to bound each individual emitted address at its own public
arena endpoint. All prefix word protection follows at every event, with no
stored per-trial receipt or estimation of the past balance. -/
theorem PriceHistory.safe {w q d : ℕ} (P : PriceHistory) (C : Chart w q d) (arena : Arena)
    (e : Event) (i : Fin (P.size (position C.mesh e)))
    (emits : ∀ t<position C.mesh e,∀ j : Fin (P.count t),
      (P.emit t j).width<arena.first+(t+1)*arena.stride ∧
      (P.emit t j).key<arena.first+(t+1)*arena.stride)
    (prior : ∀x,x<arena.base C.mesh e→protected C x e) :
    protected C (P.word (position C.mesh e) i).width e ∧ protected C (P.word (position C.mesh e) i).key e := by
  obtain ⟨t,ht,j,hj⟩ := P.source _ i
  rw [hj]
  have le : arena.first+(t+1)*arena.stride≤arena.base C.mesh e :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ ht) _
  exact ⟨prior _ ((emits t ht j).1.trans_le le),prior _ ((emits t ht j).2.trans_le le)⟩

end
end Hierarchy.ProtocolRAM.Calendar

end OAI

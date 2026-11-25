import OAI.Hierarchy.ProtocolRAMCalendarPaidHistory
import OAI.Hierarchy.ProtocolRAMCalendarFeedCash
import OAI.Hierarchy.ProtocolRAMCalendarFeedLayout

namespace OAI
/-! # Constructing the signed word history from each executed event's port reports -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
variable {w q d : ℕ} {I : Type*}

structure WordRows where
  count : ℕ
  word : Fin count→ChargeWord

def WordRows.ofPorts {J : Type*} [Fintype J] (row : J→ChargeWord) : WordRows :=
  ⟨Fintype.card J,fun i=>row ((Fintype.equivFin J).symm i)⟩

/-- Charge words of a physical chronological event, enumerated only from that
event's signed port descriptor. Out-of-calendar cursors have no payments. -/
def scheduleRows (c : Mesh) (issued : Event→WordRows) (j : ℕ) : WordRows :=
  if hj : j<(events c).length then issued ((events c)[j]) else ⟨0,Fin.elim0⟩

def postedRows (c : Mesh) (issued : Event→WordRows) : PriceHistory :=
  ⟨fun j=>(scheduleRows c issued j).count,fun j=>(scheduleRows c issued j).word⟩

theorem event_at (c : Mesh) {e : Event} (live : e∈events c) :
    ∃ fit : position c e<(events c).length,(events c)[position c e]=e := by
  obtain ⟨j,hj,h⟩ := List.getElem_of_mem live
  have key := position_at c hj
  rw [h] at key
  subst j
  exact ⟨hj,h⟩

theorem scheduleRows_current (c : Mesh) (issued : Event→WordRows) {e : Event} (live : e∈events c) :
    scheduleRows c issued (position c e)=issued e := by
  obtain ⟨fit,eq⟩ := event_at c live
  simp [scheduleRows,fit,eq]

/-- Specialized to the literal typed set of payment records, the common
ordinal index induces the new-row equivalence required by the stock and feed
price theorems. -/
def PriceHistory.extension (P : PriceHistory) (c : Mesh) (a b : Attempt) {J : Type*}
    (ports : J ≃ Fin (P.count (cursor c a))) (next : cursor c b=cursor c a+1) :
    Fin (P.size (cursor c a)) ⊕ J ≃ Fin (P.size (cursor c b)) :=
  ((Equiv.sumCongr (Equiv.refl _) ports).trans (P.extend _)).trans (finCongr (congrArg P.size next.symm))

theorem PriceHistory.extension_old (P : PriceHistory) {c : Mesh} {a b : Attempt} {J : Type*}
    (ports : J ≃ Fin (P.count (cursor c a))) (h : cursor c b=cursor c a+1) (i : Fin (P.size (cursor c a))) :
    P.word (cursor c b) (P.extension c a b ports h (.inl i))=P.word (cursor c a) i := by
  exact (P.word_cast h.symm _).trans (P.old_row (cursor c a) i)

theorem PriceHistory.extension_new (P : PriceHistory) {c : Mesh} {a b : Attempt} {J : Type*}
    (ports : J ≃ Fin (P.count (cursor c a))) (h : cursor c b=cursor c a+1) (i : J) :
    P.word (cursor c b) (P.extension c a b ports h (.inr i))=P.emit (cursor c a) (ports i) := by
  exact (P.word_cast h.symm _).trans (P.new_row (cursor c a) (ports i))

/-- Canonical new ports of a live physical event; users supply the native bank
addresses and coefficient lookups, with no cumulative-charge input. -/
def rowsEquiv (c : Mesh) (issued : Event→WordRows) {e : Event} (live : e∈events c)
    {J : Type*} [Fintype J] (row : J→ChargeWord) (kind : issued e=WordRows.ofPorts row) :
    J ≃ Fin ((postedRows c issued).count (position c e)) :=
  (Fintype.equivFin J).trans (finCongr (congrArg WordRows.count ((scheduleRows_current c issued live).trans kind)).symm)

theorem rowsEquiv_word (c : Mesh) (issued : Event→WordRows) {e : Event} (live : e∈events c)
    {J : Type*} [Fintype J] (row : J→ChargeWord) (kind : issued e=WordRows.ofPorts row) (i : J) :
    (postedRows c issued).emit (position c e) (rowsEquiv c issued live row kind i)=row i := by
  let out := scheduleRows c issued (position c e)
  have eq : out=WordRows.ofPorts row := (scheduleRows_current c issued live).trans kind
  change out.word (((Fintype.equivFin J).trans (finCongr (congrArg WordRows.count eq).symm)) i)=row i
  have read (v : WordRows) (same : v = WordRows.ofPorts row) :
      v.word (Fin.cast (congrArg WordRows.count same).symm ((Fintype.equivFin J) i)) = row i := by
    subst v
    change row ((Fintype.equivFin J).symm ((Fintype.equivFin J) i)) = row i
    rw [Equiv.symm_apply_apply]
  exact read out eq

theorem Succession.at (c : Mesh) (e : Event) : cursor c (Succession c e).1=position c e := by
  cases e with
  | attempt a => cases a <;> rfl
  | feed b => cases b <;> simp [Succession,cursor,position,sliceBase,trialBase,Nat.add_assoc]

/-- At a feed, each materialized spill count constitutes exactly one native
commodity row of the concatenated signed archive. -/
def feedPosting [Fintype I] (C : Chart w q d) (M : AccountColumns I) (issued : Event→WordRows)
    (b : Boundary) (live : Event.feed b∈events C.mesh) (overflow key : I→ℕ) (price : I→ℕ→ℝ)
    (kind : issued (.feed b)=WordRows.ofPorts (fun i=>⟨overflow i,key i,price i⟩))
    (arena : Arena)
    (fits : ∀t<position C.mesh (.feed b),∀r : Fin ((postedRows C.mesh issued).count t),
      ((postedRows C.mesh issued).emit t r).width<arena.first+(t+1)*arena.stride ∧
      ((postedRows C.mesh issued).emit t r).key<arena.first+(t+1)*arena.stride)
    (bounded : ∀x,x<arena.base C.mesh (.feed b)→protected C x (.feed b)) :
    let a := Succession C.mesh (.feed b)
    FeedPosting ((postedRows C.mesh issued).account C.mesh M) C b a.1 a.2 := by
  let e := Event.feed b
  let P := postedRows C.mesh issued
  let a := Succession C.mesh e
  have atPos : cursor C.mesh a.1=position C.mesh e := Succession.at C.mesh e
  let R : I → ChargeWord := fun i=>⟨overflow i,key i,price i⟩
  let ports := (rowsEquiv C.mesh issued live R kind).trans (finCongr (congrArg P.count atPos.symm))
  have same (i : I) : P.emit (cursor C.mesh a.1) (ports i)=R i := by
    have emit (j t : ℕ) (h : j=t) (r : Fin (P.count t)) :
        P.emit j (Fin.cast (congrArg P.count h.symm) r) = P.emit t r := by
      subst t
      rfl
    exact (emit _ _ atPos _).trans (rowsEquiv_word C.mesh issued live R kind i)
  refine ⟨overflow,key,price,P.extension C.mesh a.1 a.2 ports (Succession.next C.mesh e),?_,?_,?_⟩
  · exact P.extension_old ports (Succession.next C.mesh e)
  · exact fun i=>(P.extension_new ports (Succession.next C.mesh e) i).trans (same i)
  · intro i
    change protected C (P.word (cursor C.mesh a.1) i).width e ∧ protected C (P.word (cursor C.mesh a.1) i).key e
    rw [← P.word_cast atPos i]
    exact P.safe C arena e (Fin.cast (congrArg P.size atPos) i) fits bounded

end
end Hierarchy.ProtocolRAM.Calendar

end OAI

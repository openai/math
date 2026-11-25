import OAI.Hierarchy.ProtocolRAMCalendarPrevious
import OAI.Hierarchy.ProtocolRAMCatalystDatedPorts
import OAI.Hierarchy.ProtocolRAMCatalystArchiveCash

namespace OAI
/-! # Chronological archive entries from the signed cash and owner of each physical transaction -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open AdaptiveProbe ColumnWires Computability.VPVNP.BurstRAM PrivateRAM Calendar Calendar.StockCommit
open scoped Classical Fin.CommRing
variable {balls k K w q D count payload : ℕ}

/-- These two checked projections describe the *same* original occurrence. Its width
is written by the priced commit and its physical owner is resolved from the entry tape. -/
structure Date (chart : Chart w q D) (event : Attempt) (before : Memory w) (owner : Expr)
    (base size count payload : ℕ) where
  entry : Entry count payload
  shape : entry.rows=size
  ownerRows : PortROM owner before entry
  posted : ∀i : Fin entry.rows,after chart (.attempt event) before (base+i.val)=(entry.bits i:Word w)

/-- On each physical priced transaction the owner is read on the entered port
and its cash is read from the second committed word of that very transaction. -/
def Date.of_priced {R C H E G : Type} [Fintype C] [Fintype H] [Fintype E]
    (chart : Chart w q D) (date : Attempt) (m : Memory w) (a : StockCommit.Area)
    (s : StockCommit.Sources) (g : StockCommit.LabelSource) (batch : Batch q D)
    (physical : chart.commit date=StockCommit.pricedSegment a s g w batch)
    (active : ready chart (.attempt date) m) (board : StockCommit.EventBoard (StockCommit.fresh a s) w)
    (commit : Memory w) (snapshot : commit=StockCommit.stageInput a s g
      (PurchaseStage.postOutput (chart.layout date) (repair chart date) (prepared chart date m)))
    (plan : StockCommit.PortPlan (StockCommit.fresh a s) batch commit balls)
    (rowOrder : ∀c : Fin balls×Fin D,(plan.enum ⟨c.1,c.2⟩).val=(finProdFinEquiv c).val)
    (ballsAt : R ↪ Fin balls) (bound : Fintype.card (Role C H E k)≤D)
    (columns : R × C ↪ G) (keys : G × Fin k ↪ Fin count) (idle : Fin count)
    (positive : 0<K) (width : R→ℕ) (copies : ∀r,batch.copies≤copied K (width r) payload)
    (packet : ∀r,ballsAt r∈liveRows batch commit balls→∀c axis,cashWord plan (ballsAt r,catalystPort bound (c,axis))≤batch.copies*width r)
    (support : ∀c,0 < cashWord plan c→∃z,portCell ballsAt bound z=c)
    (owner : Expr) (source : ∀ j, owner.eval m ((finProdFinEquiv (portCell ballsAt bound j)).val:Word w)=
      ((keys (CatalystArchive.physical columns j)).val:Word w)) :
    Date chart date m owner (a.direct+a.occurrences) (balls*D) count payload :=
  ⟨readEntry plan ballsAt bound columns keys idle positive width copies packet, rfl,
    PortROM.of_readEntry plan ballsAt bound columns keys idle positive width copies packet owner m source,
    by
      subst commit
      exact priced_amount chart date m a s g batch physical active board plan rowOrder ballsAt bound columns keys
        idle positive width copies packet support⟩

def entryMemory (chart : Chart w q D) (initial : Memory w) (a : Attempt) :=
  run chart ((events chart.mesh).take (position chart.mesh (.attempt a))) initial

abbrev Dates (chart : Chart w q D) (initial : Memory w) (L : OwnerLedger) (base : Event→ℕ)
    (count payload : ℕ) :=
  ∀a,.attempt a∈events chart.mesh→
    Date chart a (entryMemory chart initial a) (L.term (.attempt a)) (base (.attempt a)) (L.rows (.attempt a)) count payload

variable {chart : Chart w q D} {initial : Memory w} {L : OwnerLedger} {base : Event→ℕ}

def issued (z : Dates chart initial L base count payload) (a : Attempt) : Entry count payload :=
  if h : .attempt a∈events chart.mesh then (z a h).entry else noneEntry count payload

def declaredRows (c : Mesh) (L : OwnerLedger) (a : Attempt) := if .attempt a∈events c then L.rows (.attempt a) else 0

theorem issued_rows (z : Dates chart initial L base count payload) (a : Attempt) :
    (issued z a).rows=declaredRows chart.mesh L a := by
  by_cases h : .attempt a∈events chart.mesh
  · simpa only [issued,dite_eq_left h,declaredRows,ite_eq_left h] using (z a h).shape
  · simp only [issued,dite_eq_right h,noneEntry,declaredRows,ite_eq_right h]

theorem issued_shape (z : Dates chart initial L base count payload) (t : Fin (events chart.mesh).length)
    (feeds : ∀b,L.rows (.feed b)=0) : (atTime chart.mesh (issued z) t).rows=L.rows ((events chart.mesh).get t) := by
  change (eventEntry (issued z) ((events chart.mesh).get t)).rows=_
  have member := (events chart.mesh).get_mem t
  cases here : (events chart.mesh).get t with
  | feed b => exact (feeds b).symm
  | attempt a =>
    rw [here] at member
    simpa only [eventEntry,issued,dite_eq_left member] using (z a member).shape

theorem issued_port (z : Dates chart initial L base count payload) (t : Fin (events chart.mesh).length)
    (a : Attempt) (here : (events chart.mesh).get t=.attempt a) :
    PortROM (L.term (.attempt a)) (run chart ((events chart.mesh).take t.val) initial) (issued z a) := by
  have member := (events chart.mesh).get_mem t
  rw [here] at member
  have n := position_at chart.mesh t.isLt
  change position chart.mesh ((events chart.mesh).get t)=t.val at n
  rw [here] at n
  simpa only [issued,dite_eq_left member,entryMemory,n] using (z a member).ownerRows

theorem issued_cash (z : Dates chart initial L base count payload) (t : Fin (events chart.mesh).length) :
    ∀j : Fin (atTime chart.mesh (issued z) t).rows,
      after chart ((events chart.mesh).get t) (run chart ((events chart.mesh).take t.val) initial)
        (base ((events chart.mesh).get t)+j.val)=((atTime chart.mesh (issued z) t).bits j:Word w) := by
  unfold atTime
  have member := (events chart.mesh).get_mem t
  have n := position_at chart.mesh t.isLt
  change position chart.mesh ((events chart.mesh).get t)=t.val at n
  cases here : (events chart.mesh).get t with
  | feed b =>
    intro j
    exact Fin.elim0 j
  | attempt a =>
    rw [here] at member n
    have chosen : issued z a=(z a member).entry := by
      unfold issued
      exact dite_eq_left member
    change ∀ j : Fin (issued z a).rows, after chart (.attempt a) (run chart ((events chart.mesh).take t.val) initial)
      (base (.attempt a)+j.val)=((issued z a).bits j:Word w)
    rw [chosen]
    simpa only [entryMemory,n] using (z a member).posted

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI

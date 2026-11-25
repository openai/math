import OAI.Hierarchy.ProtocolRAMCalendarPricedPosting
import OAI.Hierarchy.ProtocolRAMCalendarFeedStock

namespace OAI
/-! # Archived price word ranges for physical repair and feed events -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram PurchaseStage
open scoped Classical
noncomputable section
variable {z N k q d : ℕ}

def WordRows.Below (R : WordRows) (stop : ℕ) := ∀i,(R.word i).width<stop ∧ (R.word i).key<stop

theorem WordRows.below_ports {J : Type*} [Fintype J] (cells : J→ChargeWord) (stop : ℕ)
    (fits : ∀i,(cells i).width<stop ∧ (cells i).key<stop) : (WordRows.ofPorts cells).Below stop :=
  fun i=>fits ((Fintype.equivFin J).symm i)

/-- Historical billing data for each actual stamped mode of the native program.
The selector's reported threshold/menu and the purchased link's length keys are
those emitted by the live physical board itself. -/
def reportedRows (a : StockCommit.Area) (s : StockCommit.Sources) (g : StockCommit.LabelSource) (B : Repair q d)
    (routeKey : Fin a.goods→ℕ) (payload copies : ℕ) (link : Fin a.occurrences→ℕ→ℝ)
    (tree : Fin a.rows→ℕ→ℝ) (core : Fin a.goods→ℕ→ℝ) (fee : Fin a.rows→ℕ→ℝ) : WordRows :=
  WordRows.ofPorts ((StockCommit.fresh a s).eventWords B.purchaseOut payload copies
    (StockCommit.reportedKeys a g B routeKey) link tree core fee)

theorem reportedRows_below (a : StockCommit.Area) (s : StockCommit.Sources) (g : StockCommit.LabelSource)
    (B : Repair q d) (routeKey : Fin a.goods→ℕ) (payload copies : ℕ)
    (link : Fin a.occurrences→ℕ→ℝ) (tree : Fin a.rows→ℕ→ℝ) (core : Fin a.goods→ℕ→ℝ)
    (fee : Fin a.rows→ℕ→ℝ) (stop : ℕ) (area : a.stop≤ stop) (stamp : g.out+a.occurrences≤ stop)
    (menu : B.reportOut 6+a.rows≤ stop) (price : ∀i,routeKey i<stop)
    (flags : B.purchaseOut+a.rows≤ stop) (lengths : B.boughtFields 5+a.rows≤ stop) :
    (reportedRows a s g B routeKey payload copies link tree core fee).Below stop := by
  apply WordRows.below_ports
  rintro (i|i|i|i|i)
  all_goals have hi := i.isLt
  all_goals first
    | change i.val < a.occurrences at hi
    | change i.val < a.goods at hi
    | change i.val < a.rows at hi
  all_goals simp only [StockCommit.eventWords,StockCommit.eventColumns,CashColumns.addr,CashKeys.atRow,
    StockCommit.reportedKeys,StockCommit.fresh,StockCommit.Area.plan]
  all_goals obtain h := area
  all_goals dsimp only [StockCommit.Area.stop,StockCommit.Area.output,StockCommit.Area.excess,StockCommit.Area.clip,
    StockCommit.Area.src,StockCommit.Area.broadcast,StockCommit.Area.direct] at *
  all_goals first | exact ⟨by omega,price i⟩ | constructor <;> omega

/-- At a feed the cost of each physical overflow word is booked at the
corresponding route key. This includes zero-valued padded rows. -/
def spillRows (L : FeedLayout z N k) (key : FeedLayout.Good z N k→ℕ) (price : FeedLayout.Good z N k→ℕ→ℝ) :=
  WordRows.ofPorts (fun i : FeedLayout.Good z N k=>⟨L.overflow+PurchaseInventory.slot i,key i,price i⟩)

theorem spillRows_below (L : FeedLayout z N k) (key : FeedLayout.Good z N k→ℕ) (price : FeedLayout.Good z N k→ℕ→ℝ)
    (stop : ℕ) (fits : L.stop≤ stop) (keys : ∀i,key i<stop) : (spillRows L key price).Below stop := by
  apply WordRows.below_ports
  intro i
  have limit := PurchaseInventory.slot_lt i
  exact ⟨(Nat.add_lt_add_left limit L.overflow).trans_le fits,keys i⟩

/-- This yields the `fits` argument of every event cash equation from a local
layout certificate at each actual event, with no assumed bound for prior costs. -/
theorem postedRows_below (c : Mesh) (issued : Event→WordRows) (arena : Arena)
    (localFit : ∀e∈events c,(issued e).Below (arena.base c e+arena.stride))
    (j : ℕ) {r : Fin ((postedRows c issued).count j)} :
    ((postedRows c issued).emit j r).width<arena.first+(j+1)*arena.stride ∧
      ((postedRows c issued).emit j r).key<arena.first+(j+1)*arena.stride := by
  by_cases inside : j<(events c).length
  · let e := (events c)[j]
    have fits := localFit e (List.getElem_mem inside)
    have pos : position c e=j := position_at c inside
    revert r
    change (scheduleRows c issued j).Below (arena.first+(j+1)*arena.stride)
    simpa only [scheduleRows,dite_eq_left inside,Arena.base,pos,Nat.succ_mul,Nat.add_assoc] using fits
  · have no : (postedRows c issued).count j=0 := by simp [postedRows,scheduleRows,inside]
    have lt := r.isLt
    omega

end
end Hierarchy.ProtocolRAM.Calendar

end OAI

import OAI.Hierarchy.ProtocolRAMCatalystPostExtent
import OAI.Hierarchy.ProtocolRAMCalendarFeedLayout
import OAI.Hierarchy.ProtocolRAMCalendarVerdict

namespace OAI
/-! # Upper frame of the complete original priced calendar -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
open scoped Classical Fin.CommRing
variable {w q goods z d k N r edges : ℕ}

/-- A feed fills two consecutive inventories. The index and either outcome of
every pass are taken from its actual native list. -/
theorem FeedLayout.upper (L : FeedLayout z N k) (c : Mesh) (addr : Attempt→ℕ)
    (b : Boundary) (p : Pass)
    (mem : p∈L.columns.flatMap (fun f=>(f.feed c b).passes addr b)) :
    p.out+p.rows≤L.kept+2*PurchaseInventory.footprint z N k := by
  obtain ⟨col,inCols,live⟩:=List.mem_flatMap.mp mem
  obtain ⟨lane,_,rfl⟩:=List.mem_map.mp inCols
  rw [L.passes_eq c addr b lane] at live
  simp only [List.mem_cons,List.not_mem_nil,or_false] at live
  have width:=Nat.mul_le_mul_right (2^z) lane.isLt
  simp only [Nat.succ_mul] at width
  rcases live with rfl|rfl
  · change L.kept+lane.val*2^z+2^z≤L.kept+2*(FeedLayout.lanes N k*2^z)
    omega
  · change L.kept+(FeedLayout.lanes N k+lane.val)*2^z+2^z≤L.kept+2*(FeedLayout.lanes N k*2^z)
    rw [Nat.add_mul]
    omega

/-- Use native readiness at the instant each original event executes. -/
theorem upper_of_ready (C : Chart w q goods) (es : List Event) (m : Memory w) (x : ℕ)
    (live : mounted C es m) (apart : ∀e∈es,∀v, ready C e v → outside C x e) :
    run C es m x=m x := by
  induction es generalizing m with
  | nil => rfl
  | cons e es ih =>
    exact (ih (after C e m) live.2 (fun f hf=>apart f (List.mem_cons_of_mem e hf))).trans
      (after_outside C e m x live.1 (apart e List.mem_cons_self m live.1))

theorem priced_calendar_upper (c : Mesh) (finish : ℝ) (prices : PhasePrice) (A : Arena)
    (format : Attempt→Format z d k q goods) (initial width cap : ℕ) (sink : Sink r edges)
    (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (stage : ∀a,Event.attempt a∈events c→(format a).pricedArea.stop≤A.base c (.attempt a)+A.stride)
    (feed : 2*PurchaseInventory.footprint z N k≤A.stride)
    (m : PurchaseFrozen.Shelf.Mem z d) (x flag : ℕ)
    (above : A.endAddress c≤x) (flagBefore : flag<x) :
    let feeds:=feedColumns (N:=N) c A format initial width cap
    let C:=pricedInstalled c finish prices format feeds sink idBase role ids
    mounted C (events c) m→checkedOut C flag m x=m x := by
  intro feeds C live
  have same : run C (events c) m x=m x := by
    apply upper_of_ready C (events c) m x live
    intro e he v ok
    have bound:=(A.within c e he).trans above
    cases e with
    | attempt a =>
      exact priced_attempt_outside_ready c finish prices format feeds sink idBase role ids a v ok x ((stage a he).trans bound)
    | feed b =>
      intro p hp
      let L:=FeedLayout.atEvent (N:=N) c A format initial width cap b
      have h:=L.upper c C.modeAt b p hp
      exact .inr (h.trans ((Nat.add_le_add_left feed (A.base c (.feed b))).trans bound))
  exact (ProtocolRAMGeneratedWrite.frame_image flag 1 _ _ x (.inr (Nat.succ_le_of_lt flagBefore))).trans same

end Hierarchy.ProtocolRAM.Calendar
end

end OAI

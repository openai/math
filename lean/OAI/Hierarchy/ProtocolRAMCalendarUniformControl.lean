import OAI.Hierarchy.ProtocolRAMCalendarFeedRead
import OAI.Hierarchy.ProtocolRAMCalendarHardware

namespace OAI
/-! # Uniform instruction counts for chronological guards and feeds -/

namespace Hierarchy.ProtocolRAM.Calendar
open ProbeStage.Native PurchaseStage

variable {h N k w q d : ℕ}

private theorem anyMode_work (xs : List ℕ) (code : ℕ) (yes no : Expr) :
    (anyMode xs code yes no).work = xs.length*(8+yes.work)+no.work := by
  induction xs with
  | nil => simp [anyMode]
  | cons x xs ih =>
    change 6+1+yes.work+(anyMode xs code yes no).work+1=(_+1)*(8+yes.work)+no.work
    rw [ih,Nat.add_mul]
    omega

theorem stop_work (c : Mesh) (m n : Attempt→ℕ) (a : Attempt) :
    (stop c m a).work=(stop c n a).work := by
  cases a with
  | outer p a =>
    by_cases h : c.outerFuel=0 <;>
      simp [stop,outerSaturated,closed,h,anyMode_work]
  | inner p a j b =>
    by_cases h : c.innerFuel=0 <;>
      simp [stop,innerSaturated,innerClosed,h,anyMode_work,Expr.work,word]

def guardWork (c : Mesh) := ((events c).map fun e=> match e with
  | .feed _ => 0
  | .attempt a => (stop c (fun _=>0) a).work).sum

theorem guard_resources (C : Chart w q d) (a : Attempt) (occurs : .attempt a∈events C.mesh) :
    (guard C a).clock≤8+2*guardWork C.mesh ∧
    rowText (guard C a).term≤11+4*guardWork C.mesh := by
  have prior : (stop C.mesh (fun _=>0) a).work≤guardWork C.mesh :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨.attempt a,occurs,rfl⟩)
  have work : (stop C.mesh C.modeAt a).work ≤ guardWork C.mesh :=
    (stop_work C.mesh C.modeAt (fun _=>0) a).le.trans prior
  constructor
  · change 4 + 1*(2*(stop C.mesh C.modeAt a).work+4) ≤ 8+2*guardWork C.mesh
    omega
  · exact Nat.add_le_add_left (Nat.mul_le_mul_left 4 work) 11

theorem history_work (C : Chart w q d) (es : List Event) :
    (historyFlag C es).work ≤ 1+9*es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases e <;> simp only [historyFlag,word,Expr.work,List.length_cons,Nat.mul_succ] <;> omega

theorem listText_bound (ps : List Pass) (u : ℕ) (cap : ∀p∈ps,p.term.work≤u) :
    listText ps ≤ 15+ps.length*(11+4*u) := by
  induction ps with
  | nil => simp [listText]
  | cons p ps ih =>
    have one:=cap p (.head _)
    have rest:=ih (fun x hx=>cap x (.tail _ hx))
    simp only [listText,List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,rowText] at rest ⊢
    omega

theorem FeedLayout.resources (L : FeedLayout h N k) (C : Chart w q d) (b : Boundary)
    (placed : C.columns b=L.columns) :
    ticks C (.feed b)≤(4+2*FeedLayout.lanes N k*208)*2^h ∧
    eventText C (.feed b)≤15+2*FeedLayout.lanes N k*411 := by
  constructor
  · apply (L.ticks_le C b placed).trans
    have pos : 1≤2^h := Nat.one_le_two_pow
    have base : 4+2^h*204≤208*2^h := by omega
    have scale:=Nat.mul_le_mul_left (2*FeedLayout.lanes N k) base
    rw [show (4+2*FeedLayout.lanes N k*208)*2^h = 4*2^h+(2*FeedLayout.lanes N k)*(208*2^h) by ring]
    omega
  · change listText (feedPasses C b)≤_
    rw [L.generated C b placed]
    simpa only [L.schedule_length] using listText_bound (L.schedule C.mesh C.modeAt b) 100
      (fun p hp=>(L.schedule_work C.mesh C.modeAt b hp).2)

end Hierarchy.ProtocolRAM.Calendar

end OAI

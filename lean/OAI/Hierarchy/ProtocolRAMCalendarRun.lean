import OAI.Hierarchy.ProtocolRAMCalendar
import OAI.Hierarchy.ProtocolRAMPurchaseStage

namespace OAI
/-! # Linking temporal guards, frozen sampler scans, histogram repairs and scheduled feeds -/

namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open PurchaseStage
open scoped Classical Fin.CommRing
noncomputable section
variable {w q d : ℕ}

/-- Interface to a fixed native prefix, instantiated with the all-strata scan.
The calendar consumes the advertised output of this prefix at each current stock. -/
structure Prefix (w : ℕ) where
  native : Procedure w
  after : Memory w→Memory w
  ticks : ℕ
  ready : Memory w→Prop
  runs : ∀ m,ready m→native.Exec m (after m) ticks
  cheap : CheapCode native
  start : ℕ
  stop : ℕ
  frame : ∀ m a, ready m → (a<start ∨ stop≤a) → after m a=m a

/-- Sparse native commodity updates preserve all addresses outside their write ranges. -/
structure Commit (w : ℕ) where
  native : Procedure w
  after : Memory w→Memory w
  ticks : ℕ
  ready : Memory w→Prop
  runs : ∀ m,ready m→native.Exec m (after m) ticks
  cheap : CheapCode native
  keeps : ℕ→Prop
  frame : ∀ m a,ready m→keeps a→after m a=m a

structure Chart (w q d : ℕ) where
  mesh : Mesh
  modeAt : Attempt→ℕ
  stopAt : Attempt→ℕ
  frozen : Attempt→Prefix w
  commit : Attempt → Commit w
  raw : Attempt→Repair q d
  layout : Attempt→Dispatch
  columns : Boundary→List CommodityColumn

def Attempt.atInjection (c : Mesh) : Attempt→Bool
  | .outer p _ => decide (p<c.inject)
  | .inner .. => false

def Attempt.inReserve : Attempt→Bool
  | .outer .. => false
  | .inner .. => true

/-- All branch flags are read at this event's chronological input, and only a
separate boundary can return a slice or inject payload. -/
def repair (C : Chart w q d) (a : Attempt) : Repair q d :=
  let B := C.raw a
  { B with
    modeOut := C.modeAt a
    feedOnAdvance := false
    tests := { B.tests with
      stop := ⟨C.stopAt a,0⟩
      injection := a.atInjection C.mesh
      reserve := a.inReserve } }

def guard (C : Chart w q d) (a : Attempt) : Pass :=
  ⟨C.stopAt a,1,stop C.mesh C.modeAt a⟩

def feedPasses (C : Chart w q d) (b : Boundary) :=
  (C.columns b).flatMap fun f=>(f.feed C.mesh b).passes C.modeAt b

def prepared (C : Chart w q d) (a : Attempt) (m : Memory w) :=
  (C.frozen a).after ((guard C a).apply m)

def step (C : Chart w q d) : Event → Procedure w
  | .attempt a => ((guard C a).procedure w).seq
      ((C.frozen a).native.seq ((postFrozen w (C.layout a) (repair C a)).seq (C.commit a).native))
  | .feed b => program w (feedPasses C b)

def after (C : Chart w q d) : Event→Memory w→Memory w
  | .attempt a,m => (C.commit a).after (postOutput (C.layout a) (repair C a) (prepared C a m))
  | .feed b,m => result (feedPasses C b) m

def ticks (C : Chart w q d) : Event→ℕ
  | .attempt a => (guard C a).clock+((C.frozen a).ticks+(postTicks (C.layout a) (repair C a)+(C.commit a).ticks))
  | .feed b => clock (feedPasses C b)

/-- This predicate contains only storage, address ordering, source-bank and
numeric conditions for this chronological input. -/
def ready (C : Chart w q d) : Event→Memory w→Prop
  | .attempt a,m =>
    let B := repair C a
    let L := C.layout a
    let v := prepared C a m
    (guard C a).Fits w ∧ (C.frozen a).ready ((guard C a).apply m) ∧ 0<w ∧ TestsReady B v ∧
      (repairMask B).Fits w B.repairBits.base ∧ B.repairBits.base+L.candidates<2^w ∧
      AuditReady (audits L B) (postSnapshot L B v) ∧ OrderedTallies (audits L B) ∧
      (verdict (audits L B)).Fits w B.verdict ∧ B.verdict+1<2^w ∧
      (C.commit a).ready (postOutput L B v) ∧ (C.commit a).keeps B.verdict ∧
      ∀ p∈writes L B,∀ i : Fin p.rows,(C.commit a).keeps (p.out+i.val)
  | .feed b,_ => ∀ p∈feedPasses C b,p.Fits w

theorem step_exec (C : Chart w q d) (e : Event) (m : Memory w) (h : ready C e m) :
    (step C e).Exec m (after C e m) (ticks C e) := by
  cases e with
  | feed b =>
    intro P R K M pc reg pub exit rom data cfg start entry same
    exact program_exec _ _ h M pc reg pub exit rom data cfg start entry same
  | attempt a =>
    rcases h with ⟨guardFit,mounted,positive,tests,mask,room,auditsOk,order,deps,space,final,_,_⟩
    let p := guard C a
    let f := C.frozen a
    obtain ⟨post,_⟩ := postFrozen_exec (C.layout a) (repair C a) (prepared C a m)
      positive tests mask room auditsOk order deps space
    apply Procedure.Exec.then (scan_exec p.out p.rows p.term m guardFit.1 guardFit.2)
    apply Procedure.Exec.then (f.runs _ mounted)
    apply Procedure.Exec.then post
    intro P R K M pc reg pub exit rom data cfg start entry same
    exact (C.commit a).runs _ final M pc reg pub exit rom data cfg start entry same

attribute [local irreducible] CheapCode

theorem step_cheap (C : Chart w q d) (e : Event) : CheapCode (step C e) := by
  cases e with
  | feed b => exact program_cheap w (feedPasses C b)
  | attempt a =>
    let p:=guard C a
    exact cheap_seq (scan_cheap w p.out p.rows p.term) (cheap_seq (C.frozen a).cheap
      (cheap_seq (postFrozen_cheap w (C.layout a) (repair C a)) (C.commit a).cheap))

def accepted (C : Chart w q d) : Event→Memory w→Prop
  | .attempt a,m =>
    let L := C.layout a
    let B := repair C a
    ∀ j<L.candidates,(enabledBatch L B).valid (postSnapshot L B (prepared C a m)) (j:Word w)
  | .feed _,_ => True

theorem attempt_verdict (C : Chart w q d) (a : Attempt) (m : Memory w) (h : ready C (.attempt a) m) :
    after C (.attempt a) m (repair C a).verdict=0 ↔ accepted C (.attempt a) m := by
  rcases h with ⟨_,_,wide,tests,mask,room,plan,order,deps,space,final,safe,_⟩
  rw [after,(C.commit a).frame _ _ final safe]
  exact (postFrozen_exec (C.layout a) (repair C a) (prepared C a m)
    wide tests mask room plan order deps space).2

theorem attempt_read (C : Chart w q d) (a : Attempt) (m : Memory w) (h : ready C (.attempt a) m)
    (board : Board (C.layout a) (repair C a) w) (p : Pass) (hp : p∈writes (C.layout a) (repair C a))
    (i : Fin p.rows) :
    after C (.attempt a) m (p.out+i.val)=p.term.eval (postSnapshot (C.layout a) (repair C a) (prepared C a m)) (i.val:Word w) := by
  rcases h with ⟨_,_,_,_,_,_,plan,_,_,_,final,_,safe⟩
  rw [after,(C.commit a).frame _ _ final (safe p hp i)]
  exact post_read _ _ _ plan board p hp i

def code (C : Chart w q d) : List Event→Procedure w
  | [] => program w []
  | e::es => (step C e).seq (code C es)

def run (C : Chart w q d) : List Event→Memory w→Memory w
  | [],m => m
  | e::es,m => run C es (after C e m)

def cost (C : Chart w q d) (es : List Event) := (es.map (ticks C)).sum+4

def mounted (C : Chart w q d) : List Event→Memory w→Prop
  | [],_ => True
  | e::es,m => ready C e m ∧ mounted C es (after C e m)

/-- The emitted native bytes execute every attempt and boundary on the memory
left by the preceding event, including all unused selector checks and cap discharges. -/
theorem run_exec (C : Chart w q d) (es : List Event) (m : Memory w) (h : mounted C es m) :
    (code C es).Exec m (run C es m) (cost C es) := by
  induction es generalizing m with
  | nil =>
    intro P R K M pc reg pub exit rom data cfg start entry same
    exact program_exec [] m (by simp) M pc reg pub exit rom data cfg start entry same
  | cons e es ih =>
    have count : cost C (e::es)=ticks C e+cost C es := by simp [cost,Nat.add_assoc]
    rw [count]
    apply Procedure.Exec.then (step_exec C e m h.1)
    intro P R K M pc reg pub exit rom data cfg start entry same
    exact ih (after C e m) h.2 M pc reg pub exit rom data cfg start entry same

theorem run_cheap (C : Chart w q d) (es : List Event) : CheapCode (code C es) := by
  induction es with
  | nil => exact program_cheap w []
  | cons e es ih => exact cheap_seq (step_cheap C e) ih

theorem mesh_ticks (C : Chart w q d) (rowCost : ℕ) (account : ∀ e∈events C.mesh,ticks C e≤rowCost) :
    cost C (events C.mesh) ≤
      (C.mesh.inject+C.mesh.cool)*(C.mesh.outerFuel*(1+C.mesh.reserveSteps*(C.mesh.innerFuel+1))+1)*rowCost+4 := by
  have sum (xs : List Event) (hs : ∀ e∈xs,ticks C e≤rowCost) :
      (xs.map (ticks C)).sum ≤ xs.length*rowCost := by
    induction xs with
    | nil => simp
    | cons h t ih =>
      simpa [Nat.succ_mul,Nat.add_comm] using Nat.add_le_add (hs h (by simp))
        (ih (fun e he=>hs e (by simp [he])))
  simpa [cost,event_count] using Nat.add_le_add_right (sum _ account) 4

end
end Hierarchy.ProtocolRAM.Calendar

end OAI

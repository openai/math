import OAI.Hierarchy.ProtocolRAMCalendarFeedBoot
import OAI.Hierarchy.ProtocolRAMCalendarJointHeader

namespace OAI
/-! # Reopening both fixed integer tables in the priced calendar -/

namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen PurchaseStage
open ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section
variable {z d k q goods jobs w : ℕ}

def beforeTrial (c : Mesh) (p a : ℕ) : List Event :=
  (List.range p).flatMap (outerBlock c) ++ (List.range a).flatMap (trialBlock c p)

theorem trial_as_run (C : Chart w q goods) (m : Memory w) (p a : ℕ) :
    trialState C m p a=run C (beforeTrial C.mesh p a) m := by
  rw [beforeTrial,run_append]
  rfl

private theorem range_prefix_mounted (C : Chart w q goods) (m : Memory w) (f : ℕ→List Event)
    {start stop : ℕ} (inside : start ≤ stop) (fit : mounted C ((List.range stop).flatMap f) m) :
    mounted C ((List.range start).flatMap f) m := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_add_of_le inside
  rw [List.range_add,List.flatMap_append] at fit
  exact ((mounted_append C _ _ _).mp fit).1

theorem beforeTrial_mounted (C : Chart w q goods) (m : Memory w) (p a : ℕ)
    (whole : mounted C (events C.mesh) m) (hp : p<C.mesh.inject+C.mesh.cool) (ha : a≤C.mesh.outerFuel) :
    mounted C (beforeTrial C.mesh p a) m := by
  rw [beforeTrial,mounted_append]
  refine ⟨range_prefix_mounted C _ _ hp.le whole,?_⟩
  have phase := phase_mounted whole hp
  exact range_prefix_mounted C (phaseState C m p) _ ha ((mounted_append C _ _ _).mp phase).1

theorem beforeInner_mounted (C : Chart w q goods) (m : Memory w) (p a j b : ℕ)
    (whole : mounted C (events C.mesh) m) (hp : p<C.mesh.inject+C.mesh.cool) (ha : a<C.mesh.outerFuel)
    (hj : j<C.mesh.reserveSteps) (hb : b≤C.mesh.innerFuel) :
    mounted C (FeedLayout.beforeInner C.mesh p a j b) m := by
  change mounted C ((beforeTrial C.mesh p a++[Event.attempt (.outer p a)])++purchaseTail C.mesh p a j b) m
  rw [mounted_append,mounted_append,run_append,←trial_as_run]
  exact ⟨⟨beforeTrial_mounted C m p a whole hp ha.le,outer_head_ready whole hp ha,trivial⟩,
    purchaseTail_mounted whole hp ha hj hb⟩

/-- Both table origins on the unique header containing the permutation, active stock,
and every archived score page. The source for the half table already contains the
floor table below it. -/
theorem JointHeader.integer_origins {N phases : ℕ} (B : JointHeader.Board) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (rest : Boot.Tape z d)
    (v : Fin jobs→Market z d k) {size : ℕ} (layout : Boot.Layout v size) (hd : 1≤d)
    (start : 2^z≤B.initial) (heap : heapEnd z d copies≤B.initial+GlobalTests.rows z N k)
    (fits : JointHeader.stop B z N k phases ≤ size) (early : ∀ t,JointHeader.stop B z N k phases≤Boot.low (v t)) :
    let source := JointHeader.inventory B z N k stock (Boot.permutationWords π rest)
    let bank := FeedROM.sliceBank B.initial (GlobalTests.rows z N k) B.steps B.cap B.width
    let half := JointHeader.half B z N k
    let fixture := feedAdvice bank B.steps (B.cap*B.width+1) source
    let out := Boot.booted v size (JointHeader.words B z d N k phase π stock rest)
    (∀ a,bank.base≤a → a<bank.base+B.steps*(B.cap*B.width+1) → out a=fixture a) ∧
    (∀ a,half.base≤a → a<half.base+half.size → out a=FeedROM.halfAdvice half fixture a) := by
  intro source bank half fixture out
  have rom : bank.base+B.steps*(B.cap*B.width+1)≤half.base :=
    Nat.add_le_add_left (sliceROM_size (B.initial+GlobalTests.rows z N k) B.steps _) _
  have hh : bank.base≤half.base := (Nat.le_add_right ..).trans rom
  constructor
  · intro a lo hi
    have origin := JointHeader.low_origin B phase π stock rest v layout hd start fits early a (heap.trans lo)
      ((hi.trans_le rom).trans_le (Nat.le_add_right ..))
    exact origin.trans (FeedROM.slice_cell B.initial (GlobalTests.rows z N k) B.steps B.cap B.width source a hi)
  · intro a lo hi
    exact JointHeader.low_origin B phase π stock rest v layout hd start fits early a (heap.trans (hh.trans lo)) hi

namespace Boot

/-- The two timestamped prices and the old stock are observed at their genuine
chronological gate. The half table at that point is the original finite header. -/
theorem half_before_purchase (C : Chart w q goods) (arena : Arena) (mem fixture : Memory w)
    (table : Bank) (p a : ℕ) (whole : mounted C (events C.mesh) mem)
    (hp : p<C.mesh.inject+C.mesh.cool) (ha : a<C.mesh.outerFuel)
    (first : table.base+table.size≤arena.first)
    (floor : ∀ e u,u<arena.base C.mesh e→protected C u e)
    (boot : ∀ x,table.base≤x → x<table.base+table.size → mem x=FeedROM.halfAdvice table fixture x) :
    let e := Attempt.outer p a
    let current := postOutput (C.layout e) (repair C e) (prepared C e (trialState C mem p a))
    ∀ x,table.base≤x → x<table.base+table.size → current x=FeedROM.halfAdvice table fixture x := by
  intro e _ x hx hi
  have low (f : Event) : x<arena.base C.mesh f := (hi.trans_le first).trans_le (Nat.le_add_right ..)
  have prior := postOutput_prior C e (trialState C mem p a) x (outer_head_ready whole hp ha) (floor _ _ (low _))
  apply prior.trans
  rw [trial_as_run]
  exact (run_frame C _ _ x (beforeTrial_mounted C mem p a whole hp ha.le)
    (fun f _=>floor f _ (low f))).trans (boot x hx hi)

/-- All previous writes preserve the same slice ROM installed by integerHeader. -/
theorem slice_before_feed (C : Chart w q goods) (arena : Arena) (mem fixture : Memory w)
    (table : Bank) (stride p a j : ℕ) (whole : mounted C (events C.mesh) mem)
    (hp : p<C.mesh.inject+C.mesh.cool) (ha : a<C.mesh.outerFuel) (hj : j<C.mesh.reserveSteps)
    (first : table.base+C.mesh.reserveSteps*stride≤arena.first)
    (floor : ∀ e u,u<arena.base C.mesh e→protected C u e)
    (boot : ∀ x,table.base≤x → x<table.base+C.mesh.reserveSteps*stride →
      mem x=feedAdvice table C.mesh.reserveSteps stride fixture x) :
    ∀ x,table.base≤x → x<table.base+C.mesh.reserveSteps*stride →
      innerState C mem p a j C.mesh.innerFuel x=feedAdvice table C.mesh.reserveSteps stride fixture x := by
  intro x hx hi
  rw [FeedLayout.inner_as_run]
  exact (run_frame C _ _ x (beforeInner_mounted C mem p a j C.mesh.innerFuel whole hp ha hj le_rfl)
    (fun e _=>floor e _ ((hi.trans_le first).trans_le (Nat.le_add_right ..)))).trans (boot x hx hi)

end Boot
end
end Hierarchy.ProtocolRAM.Calendar

end OAI

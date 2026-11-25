import OAI.Hierarchy.ProtocolRAMCalendarTailLists
import OAI.Hierarchy.ProtocolRAMCalendarVerdict

namespace OAI
/-! # Observed before- and after-states of each segment of the native calendar -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM
open PurchaseStage
open scoped Fin.CommRing
variable {w q d : ℕ} (C : Chart w q d)

theorem run_append (xs ys : List Event) (m : Memory w) :
    run C (xs ++ ys) m = run C ys (run C xs m) := by
  induction xs generalizing m with
  | nil => rfl
  | cons e xs ih => exact ih (after C e m)

private def blocks (f : ℕ → List Event) (n : ℕ) (m : Memory w) : Memory w :=
  run C ((List.range n).flatMap f) m

private theorem blocks_succ (f : ℕ → List Event) (j : ℕ) (m : Memory w) :
    blocks C f (j+1) m = run C (f j) (blocks C f j m) := by
  simp [blocks,List.range_succ,run_append]

def phaseState (m : Memory w) (p : ℕ) : Memory w := blocks C (outerBlock C.mesh) p m

def trialState (m : Memory w) (p h : ℕ) : Memory w :=
  blocks C (trialBlock C.mesh p) h (phaseState C m p)

def reserveState (m : Memory w) (p h j : ℕ) : Memory w :=
  blocks C (reserveBlock C.mesh p h) j (after C (.attempt (.outer p h)) (trialState C m p h))

def innerState (m : Memory w) (p h j b : ℕ) : Memory w :=
  run C ((List.range b).map (fun i => .attempt (.inner p h j i))) (reserveState C m p h j)

@[simp] theorem phase_zero (m : Memory w) : phaseState C m 0 = m := rfl

@[simp] theorem trial_zero (m : Memory w) (p : ℕ) : trialState C m p 0 = phaseState C m p := rfl

@[simp] theorem reserve_zero (m : Memory w) (p h : ℕ) : reserveState C m p h 0 =
    after C (.attempt (.outer p h)) (trialState C m p h) := rfl

@[simp] theorem inner_zero (m : Memory w) (p h j : ℕ) : innerState C m p h j 0 =
    reserveState C m p h j := rfl

theorem phase_block (m : Memory w) (p : ℕ) :
    phaseState C m (p+1)=run C (outerBlock C.mesh p) (phaseState C m p) :=
  blocks_succ C (outerBlock C.mesh) p m

theorem reserve_block (m : Memory w) (p h j : ℕ) :
    reserveState C m p h (j+1)=run C (reserveBlock C.mesh p h j) (reserveState C m p h j) :=
  blocks_succ C (reserveBlock C.mesh p h) j _

theorem phase_succ (m : Memory w) (p : ℕ) :
    phaseState C m (p+1) = after C (.feed (.outer p)) (trialState C m p C.mesh.outerFuel) := by
  unfold phaseState
  rw [blocks_succ,outerBlock,run_append]
  rfl

theorem trial_succ (m : Memory w) (p h : ℕ) :
    trialState C m p (h+1) = reserveState C m p h C.mesh.reserveSteps := by
  unfold trialState
  rw [blocks_succ]
  rfl

theorem reserve_succ (m : Memory w) (p h j : ℕ) :
    reserveState C m p h (j+1) = after C (.feed (.inner p h j))
      (innerState C m p h j C.mesh.innerFuel) := by
  unfold reserveState
  rw [blocks_succ,reserveBlock,run_append]
  rfl

theorem inner_succ (m : Memory w) (p h j b : ℕ) :
    innerState C m p h j (b+1) = after C (.attempt (.inner p h j b)) (innerState C m p h j b) := by
  simp [innerState,List.range_succ,run_append,run]

theorem final_phase (m : Memory w) : run C (events C.mesh) m =
    phaseState C m (C.mesh.inject+C.mesh.cool) := rfl

/-- The discriminant used by the finite repair ledger is the instruction's
actual read of the frozen, tested memory at this chronological outer trial. -/
def observedMode (m : Memory w) (p h : ℕ) : ℕ :=
  let a := Attempt.outer p h
  let B := repair C a
  AttemptGate.actual B.policy (postSnapshot (C.layout a) B (prepared C a (trialState C m p h)))

theorem observedMode_lt (m : Memory w) (p h : ℕ) : observedMode C m p h < 4 :=
  AttemptGate.actual_lt _ _

theorem observed_mode_word (m : Memory w) (p h : ℕ) (i : Fin (C.layout (.outer p h)).candidates)
    (mountedHead : ready C (.attempt (.outer p h)) (trialState C m p h))
    (board : Board (C.layout (.outer p h)) (repair C (.outer p h)) w) :
    reserveState C m p h 0 (C.modeAt (.outer p h)+i.val) = (observedMode C m p h : Word w) := by
  let a := Attempt.outer p h
  let L := C.layout a
  let B := repair C a
  let v := prepared C a (trialState C m p h)
  change after C (.attempt a) (trialState C m p h) (B.modeOut+i.val) = _
  exact (attempt_read C a (trialState C m p h) mountedHead board ⟨B.modeOut,L.candidates,AttemptGate.mode B.policy⟩
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) i).trans (AttemptGate.mode_eval ..)

theorem mounted_append (xs ys : List Event) (m : Memory w) :
    mounted C (xs++ys) m ↔ mounted C xs m ∧ mounted C ys (run C xs m) := by
  induction xs generalizing m with
  | nil => simp [mounted,run]
  | cons e xs ih => simp only [List.cons_append,mounted,run,ih,and_assoc]

/-- Events strictly after the observed outer verdict through the start of a later outer
trial in the same phase. These include all reserve feeds of the producing trial. -/
theorem trial_tail (m : Memory w) (p h extra : ℕ) :
    trialState C m p (h+1+extra) = run C (trialTail C.mesh p h extra) (reserveState C m p h 0) := by
  change run C ((List.range ((h+1)+extra)).flatMap _) _ = _
  rw [List.range_add,List.flatMap_append,run_append]
  change run C _ (trialState C m p (h+1)) = _
  rw [trial_succ,trialTail,run_append]
  rfl

theorem trial_archive (m : Memory w) (p h extra addr : ℕ)
    (ready : mounted C (trialTail C.mesh p h extra) (reserveState C m p h 0))
    (safe : ∀ e∈trialTail C.mesh p h extra, protected C addr e) :
    trialState C m p (h+1+extra) addr = reserveState C m p h 0 addr := by
  rw [trial_tail]
  exact run_frame C _ _ _ ready safe

/-- The same authenticated mode word may be read after its phase's last actual
scheduled feed and at any trial of any subsequent phase. -/
theorem phase_tail (m : Memory w) (p h extra b : ℕ) (inside : h<C.mesh.outerFuel) :
    trialState C m (p+1+extra) b = run C (phaseTail C.mesh p h extra b) (reserveState C m p h 0) := by
  have tail : trialState C m p C.mesh.outerFuel =
      run C (trialTail C.mesh p h (C.mesh.outerFuel-(h+1))) (reserveState C m p h 0) := by
    simpa only [Nat.add_sub_of_le (by omega : h+1≤C.mesh.outerFuel)] using
      trial_tail C m p h (C.mesh.outerFuel-(h+1))
  change run C _ (run C ((List.range ((p+1)+extra)).flatMap _) m) = _
  rw [List.range_add,List.flatMap_append,run_append]
  change run C _ (run C _ (phaseState C m (p+1))) = _
  rw [phase_succ,tail]
  simp only [phaseTail,run_append,run]

theorem phase_archive (m : Memory w) (p h extra b addr : ℕ) (inside : h<C.mesh.outerFuel)
    (ready : mounted C (phaseTail C.mesh p h extra b) (reserveState C m p h 0))
    (safe : ∀ e∈phaseTail C.mesh p h extra b, protected C addr e) :
    trialState C m (p+1+extra) b addr = reserveState C m p h 0 addr := by
  rw [phase_tail C m p h extra b inside]
  exact run_frame C _ _ _ ready safe

def observedInnerMode (m : Memory w) (p h j b : ℕ) : ℕ :=
  let a := Attempt.inner p h j b
  let B := repair C a
  AttemptGate.actual B.policy (postSnapshot (C.layout a) B (prepared C a (innerState C m p h j b)))

theorem inner_mode_word (m : Memory w) (p h j b : ℕ) (i : Fin (C.layout (.inner p h j b)).candidates)
    (mountedHead : ready C (.attempt (.inner p h j b)) (innerState C m p h j b))
    (board : Board (C.layout (.inner p h j b)) (repair C (.inner p h j b)) w) :
    innerState C m p h j (b+1) (C.modeAt (.inner p h j b)+i.val) =
      (observedInnerMode C m p h j b : Word w) := by
  let a := Attempt.inner p h j b
  let L := C.layout a
  let B := repair C a
  let v := prepared C a (innerState C m p h j b)
  rw [inner_succ]
  change after C (.attempt a) (innerState C m p h j b) (B.modeOut+i.val) = _
  exact (attempt_read C a (innerState C m p h j b) mountedHead board ⟨B.modeOut,L.candidates,AttemptGate.mode B.policy⟩
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) i).trans (AttemptGate.mode_eval ..)

theorem inner_tail (m : Memory w) (p h j b extra : ℕ) :
    innerState C m p h j (b+1+extra) =
      run C (innerTail p h j b extra) (innerState C m p h j (b+1)) := by
  change run C ((List.range ((b+1)+extra)).map _) _ = _
  rw [List.range_add,List.map_append,run_append]
  rfl

theorem inner_archive (m : Memory w) (p h j b extra addr : ℕ)
    (ready : mounted C (innerTail p h j b extra) (innerState C m p h j (b+1)))
    (safe : ∀ e∈innerTail p h j b extra, protected C addr e) :
    innerState C m p h j (b+1+extra) addr = innerState C m p h j (b+1) addr := by
  rw [inner_tail]
  exact run_frame C _ _ _ ready safe

theorem reserve_tail (m : Memory w) (p h j b extra trial : ℕ) (inside : b<C.mesh.innerFuel) :
    innerState C m p h (j+1+extra) trial = run C (reserveTail C.mesh p h j b extra trial)
      (innerState C m p h j (b+1)) := by
  have tail : innerState C m p h j C.mesh.innerFuel = run C (innerTail p h j b (C.mesh.innerFuel-(b+1)))
      (innerState C m p h j (b+1)) := by
    simpa only [Nat.add_sub_of_le (by omega : b+1≤C.mesh.innerFuel)] using
      inner_tail C m p h j b (C.mesh.innerFuel-(b+1))
  change run C _ (run C ((List.range ((j+1)+extra)).flatMap _) _) = _
  rw [List.range_add,List.flatMap_append,run_append]
  change run C _ (run C _ (reserveState C m p h (j+1))) = _
  rw [reserve_succ,tail]
  simp only [reserveTail,run_append,run]

theorem reserve_archive (m : Memory w) (p h j b extra trial addr : ℕ) (inside : b<C.mesh.innerFuel)
    (ready : mounted C (reserveTail C.mesh p h j b extra trial) (innerState C m p h j (b+1)))
    (safe : ∀ e∈reserveTail C.mesh p h j b extra trial, protected C addr e) :
    innerState C m p h (j+1+extra) trial addr = innerState C m p h j (b+1) addr := by
  rw [reserve_tail C m p h j b extra trial inside]
  exact run_frame C _ _ _ ready safe

def observedHistory (C : Chart w q d) (mem : Memory w) : Attempt → ℕ
  | .outer p h => observedMode C mem p h
  | .inner p h j b => observedInnerMode C mem p h j b

/-- From an outer mode word's production to any later inner trial of the
same purchase, including the intervening complete reserve boundaries. -/
theorem purchase_archive (m : Memory w) (p h j b addr : ℕ)
    (ready : mounted C (purchaseTail C.mesh p h j b) (reserveState C m p h 0))
    (safe : ∀ e∈purchaseTail C.mesh p h j b, protected C addr e) :
    innerState C m p h j b addr=reserveState C m p h 0 addr := by
  have state : innerState C m p h j b =
      run C (purchaseTail C.mesh p h j b) (reserveState C m p h 0) := by
    rw [purchaseTail,run_append]
    rfl
  rw [state]
  exact run_frame C _ _ _ ready safe

end Hierarchy.ProtocolRAM.Calendar
end

end OAI

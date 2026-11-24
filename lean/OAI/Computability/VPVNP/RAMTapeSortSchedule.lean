import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.TallyStacks
import OAI.Computability.VPVNP.RAMSortCostLayout

/-!
# Finite control for the bitonic phase and stride loops

Start with one unary mark for each bit of the global wire address. Each
outer pop advances the phase. A preserved copy of the new phase drives
the inner loop, which presents the exponents in descending order. The
layer routine sees the actual unary phase and stride while it works on
the site's bit stacks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortSchedule

open RAMSort Routine

/-- Unary loop counters and scratch stack for the phase and descending-stride loops of bitonic
sorting. -/
inductive Control | remaining | phase | stride | tmp
  deriving DecidableEq

instance : Fintype Control := derive_fintype% _

/-- Sorting schedule registers formed from the loop-control stacks and the caller's layer
registers. -/
abbrev Port (K : Type) := Control ⊕ K

/-- Initialize the remaining, phase, and stride stacks with unary marks, clear the temporary
stack, and retain the caller's data. -/
def bank {K : Type} (s : Stacks K) (left a j : ℕ) : Stacks (Port K)
  | .inl .remaining => List.replicate left true
  | .inl .phase => List.replicate a true
  | .inl .stride => List.replicate j true
  | .inl .tmp => []
  | .inr k => s k

variable {K : Type} [DecidableEq K]

private def copyPhase : FiniteRoutine (Port K) :=
  (FiniteRoutine.ofRoutine (Tally.copyAdd Control.phase .stride .tmp)).onPorts Sum.inl

private theorem copyPhase_run (s : Stacks K) (left a : ℕ) :
    copyPhase.Runs (5*a+2) (bank s left a 0) (bank s left a a) := by
  let registers : Tally.State Control
    | .remaining => left
    | .phase => a
    | _ => 0
  have h := Tally.copyAdd_runs Control.phase .stride .tmp (by decide) (by decide) (by decide) registers rfl
  apply FiniteRoutine.runs_onPorts_framed _ Sum.inl_injective h
  · intro i; cases i <;> rfl
  · intro i; cases i <;> simp [bank, Tally.encode, registers, Function.update]
  · rintro (i|k) h
    · exact (h i rfl).elim
    · rfl

private theorem change_left (s : Stacks K) (left next a j : ℕ) :
    Function.update (bank s left a j) (.inl .remaining) (List.replicate next true) = bank s next a j := by
  funext k; rcases k with c | k; cases c <;> simp [bank]; simp [bank]

private theorem change_stride (s : Stacks K) (left a j next : ℕ) :
    Function.update (bank s left a j) (.inl .stride) (List.replicate next true) = bank s left a next := by
  funext k; rcases k with c | k; cases c <;> simp [bank]; simp [bank]

private theorem incPhase_run (s : Stacks K) (left a : ℕ) :
    (push (Sum.inl Control.phase) true).Runs 1 (bank s left a 0) (bank s left (a+1) 0) := by
  convert runs_push (Sum.inl Control.phase) true (bank s left a 0) using 1
  funext i; rcases i with c | k; cases c <;> simp [bank, List.replicate_succ]; simp [bank]

variable (layer : FiniteRoutine (Port K))

private def eachStride : FiniteRoutine (Port K) :=
  .ofRoutine (popLoop (.inl .stride) (fun _ => true) (halt false) layer.body)

private def phaseBody : FiniteRoutine (Port K) :=
  ((FiniteRoutine.ofRoutine (push (Sum.inl Control.phase) true)).followedBy copyPhase).followedBy (eachStride layer)

/-- The stage counter lives on four bit stacks. Only the finite layer
control is incorporated into the surrounding transition table. -/
def program : FiniteRoutine (Port K) :=
  .ofRoutine (popLoop (.inl .remaining) (fun _ => true) (halt false) (phaseBody layer).body)

variable {X : Type*} {b : ℕ} (view : X → Stacks K) (next : X → Stage b → X) (limit : ℕ)

/-- The callback updates its data and preserves the phase and stride ports. -/
def LayerRuns : Prop :=
  ∀ (s : Stage b) (left : ℕ) (x : X), ∃ t ≤ limit,
    layer.Runs t (bank (view x) left s.phase s.stride) (bank (view (next x s)) left s.phase s.stride)

private theorem strides_run (h : LayerRuns layer view next limit) (a left : ℕ) (ha : a ≤ b)
    (k : ℕ) (hk : k ≤ a) (x : X) :
    ∃ t ≤ k*(limit+1)+1, (eachStride layer).Runs t (bank (view x) left a k)
      (bank (view ((strides b a ha k hk).foldl next x)) left a 0) := by
  induction k generalizing x with
  | zero =>
    simp only [strides, List.foldl_nil, eachStride, FiniteRoutine.Runs, FiniteRoutine.ofRoutine]
    exact ⟨1, by simp, Runs.popLoop_empty (Sum.inl Control.stride) (fun _ => true) (halt false) layer.body
      (s := bank (view x) left a 0) rfl⟩
  | succ k ih =>
    let s : Stage b := ⟨a, k, hk, ha⟩
    obtain ⟨u, hu, hc⟩ := h s left x
    obtain ⟨t, ht, htail⟩ := ih (by omega) (next x s)
    simp only [eachStride, FiniteRoutine.Runs, FiniteRoutine.ofRoutine] at htail
    have hh : (bank (view x) left a (k+1)) (.inl .stride) = true :: List.replicate k true := List.replicate_succ
    have run := Runs.popLoop_true_continue (Sum.inl Control.stride) (fun _ => true) (halt false) layer.body hh rfl
      (by rw [change_stride]; exact hc) htail
    refine ⟨_, ?_, run⟩
    rw [Nat.succ_mul]
    omega

private theorem phase_run (h : LayerRuns layer view next limit) (a left : ℕ) (ha : a+1 ≤ b) (x : X) :
    ∃ t ≤ 1 + (5*(a+1)+2) + ((a+1)*(limit+1)+1),
      (phaseBody layer).Runs t (bank (view x) left a 0)
        (bank (view ((strides b (a+1) ha (a+1) le_rfl).foldl next x)) left (a+1) 0) := by
  obtain ⟨t, ht, hh⟩ := strides_run layer view next limit h (a+1) left ha (a+1) le_rfl x
  have inc : (FiniteRoutine.ofRoutine (push (.inl Control.phase) true)).Runs 1
      (bank (view x) left a 0) (bank (view x) left (a+1) 0) := incPhase_run ..
  exact ⟨_, by omega, (inc.followedBy (copyPhase_run (view x) left (a+1))).followedBy hh⟩

private theorem remaining_run (h : LayerRuns layer view next limit) (x : X) (left a : ℕ) (htotal : a+left=b) :
    ∃ t ≤ left*((limit+6)*b+5)+1,
      (program layer).Runs t (bank (view ((phases b a (by omega)).foldl next x)) left a 0)
        (bank (view ((phases b b le_rfl).foldl next x)) 0 b 0) := by
  induction left generalizing a with
  | zero =>
    simp only [Nat.add_zero] at htotal
    subst b
    exact ⟨1, by simp, Runs.popLoop_empty (Sum.inl Control.remaining) (fun _ => true) (halt false)
      (phaseBody layer).body (s := bank (view ((phases a a le_rfl).foldl next x)) 0 a 0) rfl⟩
  | succ left ih =>
    let y := (phases b a (by omega)).foldl next x
    obtain ⟨u, hu, hc⟩ := phase_run layer view next limit h a left (by omega) y
    obtain ⟨t, ht, tail⟩ := ih (a+1) (by omega)
    simp only [program, FiniteRoutine.Runs, FiniteRoutine.ofRoutine] at tail
    have hs : (phases b (a+1) (by omega)).foldl next x = (strides b (a+1) (by omega) (a+1) le_rfl).foldl next y := by rw [phases, List.foldl_append]
    rw [hs] at tail
    have hh : bank (view y) (left+1) a 0 (.inl .remaining) = true :: List.replicate left true := List.replicate_succ
    have run := Runs.popLoop_true_continue (Sum.inl Control.remaining) (fun _ => true) (halt false)
      (phaseBody layer).body hh rfl (by rw [change_left]; exact hc) tail
    refine ⟨_, ?_, run⟩
    have hbound : 1+(1+(5*(a+1)+2)+((a+1)*(limit+1)+1)) ≤ (limit+6)*b+5 := calc
      _ = (limit+6)*(a+1)+5 := by ring
      _ ≤ _ := by gcongr; omega
    rw [Nat.succ_mul]
    omega

/-- From the initial unary global width, run every prescribed layer once
in chronological order. No address-width-dependent transition table is used. -/
theorem runs (h : LayerRuns layer view next limit) (x : X) :
    ∃ t ≤ b*((limit+6)*b+5)+1,
      (program layer).Runs t (bank (view x) b 0 0)
        (bank (view ((phases b b le_rfl).foldl next x)) 0 b 0) :=
  remaining_run layer view next limit h x b 0 (by omega)


/-- A bounded execution of each callback on the successive actual buffers.
This version permits callbacks whose run depends on having the appropriate
send and receive blocks at the front of the stream. -/
inductive Visits {b : ℕ} (layer : FiniteRoutine (Port K)) (limit : ℕ) :
    List (Stage b) → Stacks K → Stacks K → Prop
  | nil (x) : Visits layer limit [] x x
  | cons {s ss x y z t} (ht : t ≤ limit)
      (run : layer.Runs t (bank x (b-s.phase) s.phase s.stride) (bank y (b-s.phase) s.phase s.stride))
      (rest : Visits layer limit ss y z) : Visits layer limit (s::ss) x z

private theorem Visits.split {b : ℕ} {layer : FiniteRoutine (Port K)} {limit : ℕ}
    (ls rs : List (Stage b)) {x z : Stacks K} (h : Visits layer limit (ls++rs) x z) :
    ∃ y, Visits layer limit ls x y ∧ Visits layer limit rs y z := by
  induction ls generalizing x with
  | nil => exact ⟨x, .nil _, h⟩
  | cons s ss ih =>
    cases h with
    | cons ht run rest =>
      obtain ⟨y, first, tail⟩ := ih rest
      exact ⟨y, .cons ht run first, tail⟩

private theorem traceStrides {b limit : ℕ} (a : ℕ) (ha : a ≤ b) (k : ℕ) (hk : k ≤ a)
    {x z : Stacks K} (h : Visits layer limit (strides b a ha k hk) x z) :
    ∃ t ≤ k*(limit+1)+1, (eachStride layer).Runs t (bank x (b-a) a k) (bank z (b-a) a 0) := by
  induction k generalizing x with
  | zero =>
    cases h
    exact ⟨1, by simp, Runs.popLoop_empty (Sum.inl Control.stride) (fun _ => true) (halt false) layer.body
      (s := bank z (b-a) a 0) rfl⟩
  | succ k ih =>
    cases h with
    | @cons _ _ _ y _ u hu hc rest =>
      obtain ⟨t, ht, tail⟩ := ih (by omega) rest
      simp only [eachStride, FiniteRoutine.Runs, FiniteRoutine.ofRoutine] at tail
      have hh : bank x (b-a) a (k+1) (.inl .stride) = true :: List.replicate k true := List.replicate_succ
      have run := Runs.popLoop_true_continue (Sum.inl Control.stride) (fun _ => true) (halt false) layer.body hh rfl
        (by rw [change_stride]; exact hc) tail
      refine ⟨_, ?_, run⟩
      rw [Nat.succ_mul]
      omega

/-- The unvisited phase suffix after finishing phase `a`. -/
private def future (b a : ℕ) : (k : ℕ) → a+k ≤ b → List (Stage b)
  | 0, _ => []
  | k+1, h =>
    strides b (a+1) (by omega) (a+1) le_rfl ++ future b (a+1) k (by omega)

private theorem phases_future (b a k : ℕ) (h : a+k ≤ b) :
    phases b a (by omega) ++ future b a k h = phases b (a+k) h := by
  induction k generalizing a with
  | zero => simp [future]
  | succ k ih =>
    rw [future, ← List.append_assoc, ← phases]
    simpa only [Nat.add_assoc, Nat.add_comm 1 k] using ih (a+1) (by omega)

private theorem traceFuture {b limit : ℕ} (a k : ℕ) (hk : a+k=b) {x z : Stacks K}
    (h : Visits layer limit (future b a k hk.le) x z) :
    ∃ t ≤ k*((limit+6)*b+5)+1, (program layer).Runs t (bank x k a 0) (bank z 0 b 0) := by
  induction k generalizing a x with
  | zero =>
    cases h
    simp only [Nat.add_zero] at hk
    subst b
    exact ⟨1, by simp, Runs.popLoop_empty (Sum.inl Control.remaining) (fun _ => true) (halt false)
      (phaseBody layer).body (s := bank z 0 a 0) rfl⟩
  | succ k ih =>
    rw [future] at h
    obtain ⟨y, first, rest⟩ := h.split _ _
    obtain ⟨t, ht, hstr⟩ := traceStrides layer (a+1) (by omega) (a+1) le_rfl first
    rw [show b-(a+1)=k by omega] at hstr
    have inc : (FiniteRoutine.ofRoutine (push (.inl Control.phase) true)).Runs 1
        (bank x k a 0) (bank x k (a+1) 0) := incPhase_run ..
    have body := (inc.followedBy (copyPhase_run x k (a+1))).followedBy hstr
    obtain ⟨v, hv, tail⟩ := ih (a+1) (by omega) rest
    simp only [program, FiniteRoutine.Runs, FiniteRoutine.ofRoutine] at tail
    have hh : bank x (k+1) a 0 (.inl .remaining) = true :: List.replicate k true := List.replicate_succ
    have run := Runs.popLoop_true_continue (Sum.inl Control.remaining) (fun _ => true) (halt false)
      (phaseBody layer).body hh rfl (by rw [change_left]; exact body) tail
    refine ⟨_, ?_, run⟩
    have hbound : 1+(1+(5*(a+1)+2)+((a+1)*(limit+1)+1)) ≤ (limit+6)*b+5 := calc
      _ = (limit+6)*(a+1)+5 := by ring
      _ ≤ _ := by gcongr; omega
    rw [Nat.succ_mul k]
    omega

/-- Each callback need only run on the state it actually receives. -/
theorem runs_of_visits {b limit : ℕ} {x z : Stacks K} (h : Visits layer limit (phases b b le_rfl) x z) :
    ∃ t ≤ b*((limit+6)*b+5)+1, (program layer).Runs t (bank x b 0 0) (bank z 0 b 0) := by
  have eq : future b 0 b (by omega) = phases b b le_rfl := by
    simpa only [phases, List.nil_append, Nat.zero_add] using phases_future b 0 b (by omega)
  apply traceFuture layer 0 b (by omega)
  rwa [eq]


/-- Compose stage computations that consume a chronological suffix of the
incident stream. Local stages take an empty prefix. The final stage returns
whatever tail the caller placed after the sorting fields. -/
theorem Visits.of_stream {b limit : ℕ} (layer : FiniteRoutine (Port K)) {A : Type*}
    (data : A → List Bool → Stacks K) (update : A → Stage b → A) (field : Stage b → List Bool)
    (one : ∀ (x : A) (s : Stage b) (tail : List Bool), ∃ t ≤ limit,
      layer.Runs t (bank (data x (field s ++ tail)) (b-s.phase) s.phase s.stride)
        (bank (data (update x s) tail) (b-s.phase) s.phase s.stride))
    (ss : List (Stage b)) (x : A) (tail : List Bool) :
    Visits layer limit ss (data x (ss.flatMap field ++ tail)) (data (ss.foldl update x) tail) := by
  induction ss generalizing x with
  | nil => exact .nil _
  | cons s ss ih =>
    obtain ⟨t, ht, h⟩ := one x s (ss.flatMap field ++ tail)
    rw [List.flatMap_cons, List.append_assoc]
    exact .cons ht h (ih (update x s))

end RAMTape.SortSchedule

end VPVNP
end Computability
end OAI

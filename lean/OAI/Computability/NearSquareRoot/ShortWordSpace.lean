import OAI.Computability.NearSquareRoot.ShortWordStack
import OAI.Computability.NearSquareRoot.VisitedCells

/-!
# Prefix bounds for stack compilation

A uniform cap on the live height of a compiled stack gives one absolute
interval containing every physical head position, including the intermediate
step of the two-step compiler. Repeated visits consume no extra cells.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication

/-- Split an exact execution after any specified number of its transitions. -/
theorem trace_split {X : Type*} {s : X → Option X} {x y : X} {n k : ℕ}
    (run : Trace s x n y) (hk : k ≤ n) :
    ∃ z, Trace s x k z ∧ Trace s z (n-k) y := by
  induction run generalizing k with
  | nil x =>
    have : k = 0 := by omega
    subst k
    exact ⟨x, .nil _, .nil _⟩
  | @cons x u y n step rest ih =>
    cases k with
    | zero => exact ⟨x, .nil _, by simpa using Trace.cons step rest⟩
    | succ k =>
      obtain ⟨z, hx, hy⟩ := ih (k := k) (by omega)
      exact ⟨z, by simpa [Nat.add_comm] using Trace.cons step hx, by simpa [Nat.add_comm] using hy⟩

/-- Space of a compiled stack measured at an arbitrary physical prefix.
The additive cell on either side permits odd-time intermediate configurations. -/
theorem stack_fence {A Q I : Type} {m : SM.Rule A Q I} {x y : SM.Config A Q I} {n : ℕ}
    (run : Trace (SM.advance m) x n y)
    (T : I → TM.Tape (Option A)) (repr : SM.faithful x.stack T)
    (i : I) (capacity : ℕ)
    (space : ∀ {k u}, k ≤ n → Trace (SM.advance m) x k u → (u.stack i).length ≤ capacity)
    {t : ℕ} {z : TM.Config (Option A) (SM.PC A Q I) I} (ht : t ≤ 2*n)
    (segment : Trace (TM.advance (SM.toTM m)) ⟨.inl x.pc, T⟩ t z) :
    let bottom := (T i).pos + ((x.stack i).length : ℤ)
    bottom - capacity - 1 ≤ (z.tape i).pos ∧ (z.tape i).pos ≤ bottom + 1 := by
  have k_le : t / 2 ≤ n := by omega
  obtain ⟨u, sub, _⟩ := trace_split run k_le
  obtain ⟨U, _, bottom, even⟩ := simulateWithBottom sub T repr
  obtain ⟨v, head, tail⟩ := trace_split (k := 2*(t/2)) segment (by omega)
  have eq := trace_endpoint_unique head even
  subst v
  have end_pos := head_excursion tail i
  have fit := space k_le sub
  have B := bottom i
  change (U i).pos - ((t - 2 * (t / 2) : ℕ) : ℤ) ≤ (z.tape i).pos ∧
    (z.tape i).pos ≤ (U i).pos + ((t - 2 * (t / 2) : ℕ) : ℤ) at end_pos
  dsimp only
  omega

/-- The fixed compiler uses at most the sum of the per-stack height caps plus three
cells per tape. Its physical head coordinates may start at unrelated addresses. -/
theorem visitsAtMost_of_stack_heights {A Q I : Type} [Fintype I] {m : SM.Rule A Q I}
    {x y : SM.Config A Q I} {n : ℕ} (run : Trace (SM.advance m) x n y)
    (T : I → TM.Tape (Option A)) (repr : SM.faithful x.stack T) (capacity : I → ℕ)
    (height : ∀ {k u}, k ≤ n → Trace (SM.advance m) x k u →
      ∀ i, (u.stack i).length ≤ capacity i) :
    VisitsAtMost (SM.toTM m) ⟨.inl x.pc, T⟩ (2 * n) (∑ i : I, (capacity i + 3)) := by
  let bottom (i : I) := (T i).pos + ((x.stack i).length : ℤ)
  have cover := visitsAtMost_of_tape_fences (fun i => bottom i - capacity i - 1)
    (fun i => bottom i + 1) (fun t ht z h i =>
      stack_fence run T repr i (capacity i) (fun hk sub => height hk sub i) ht h)
  convert cover using 1
  congr 1
  funext i
  omega

section
variable {A Q I : Type} {m : TM.Rule A Q I} {lo hi : I → ℤ}
  {x y z : TM.Config A Q I} {s t : ℕ}

/-- A physical run whose heads stay in the given absolute tape intervals. -/
def FencedRun (m : TM.Rule A Q I) (lo hi : I → ℤ) (x : TM.Config A Q I) (t : ℕ)
    (z : TM.Config A Q I) : Prop :=
  Trace (TM.advance m) x t z ∧
    ∀ u ≤ t, ∀ c, Trace (TM.advance m) x u c → ∀ i,
      lo i ≤ (c.tape i).pos ∧ (c.tape i).pos ≤ hi i

/-- Sequential calls on the same physical tapes share all previously visited cells
inside their common fences. Their clocks add. -/
theorem FencedRun.trans (left : FencedRun m lo hi x s y)
    (right : FencedRun m lo hi y t z) : FencedRun m lo hi x (s + t) z := by
  refine ⟨left.1.trans right.1, fun u hu c hx i => ?_⟩
  by_cases h : u ≤ s
  · exact left.2 u h c hx i
  obtain ⟨mid, first, last⟩ := trace_split hx (k := s) (by omega)
  have e := trace_endpoint_unique first left.1
  subst mid
  exact right.2 (u - s) (by omega) c last i

/-- Any record call of duration at most a local clock fits in that radius around its
starting heads. A new call can reuse these same intervals after restoring its heads. -/
theorem fencedRun_of_call_clock (run : Trace (TM.advance m) x t y) (clock : ℕ)
    (budget : t ≤ clock) (start : ∀ i,
      lo i + clock ≤ (x.tape i).pos ∧ (x.tape i).pos ≤ hi i - clock) :
    FencedRun m lo hi x t y := by
  refine ⟨run, fun u hu c hx i => ?_⟩
  obtain ⟨a, b⟩ := head_excursion hx i
  obtain ⟨c, d⟩ := start i
  omega

theorem FencedRun.visitsAtMost [Fintype I] (run : FencedRun m lo hi x t z) :
    VisitsAtMost m x t (∑ i, (hi i + 1 - lo i).toNat) :=
  visitsAtMost_of_tape_fences lo hi run.2

end

end NearSquareRoot
end Computability
end OAI

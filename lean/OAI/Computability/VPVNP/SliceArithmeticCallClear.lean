import OAI.Computability.VPVNP.RAMTapeISAPorts

/-! # Reclaiming the finite workspace of a slice-field multiplication call -/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.CallClear

open RAMTape

variable {K : Type} [DecidableEq K]

/-- Discard the bits on one port and return on the first empty pop. -/
def clear (k : K) : FiniteRoutine K := FiniteRoutine.ofRoutine {
  entry := ()
  code := fun _ => .pop k fun b => b.map fun _ => () }

theorem clear_runs (k : K) (s : Stacks K) :
    (clear k).Runs ((s k).length + 1) s (Function.update s k []) := by
  generalize h : s k = bits
  induction bits generalizing s with
  | nil =>
    have step := StackStep.pop (s := s) (code := (clear k).body.standalone)
      (q := some ()) (show (clear k).body.standalone (some ()) = .pop k (fun b => b.map fun _ => ()) from rfl)
    rw [h] at step
    exact .cons step (.nil ..)
  | cons b bs ih =>
    have step := StackStep.pop (s := s) (code := (clear k).body.standalone)
      (q := some ()) (show (clear k).body.standalone (some ()) = .pop k (fun x => x.map fun _ => ()) from rfl)
    rw [h] at step
    have run := ih (Function.update s k bs) (Function.update_self ..)
    rw [Function.update_idem] at run
    exact .cons step run

/-- A fixed table of ports to erase before a normal return. -/
def cleanup : List K → FiniteRoutine K
  | [] => .ret
  | i :: is => (clear i).followedBy (cleanup is)

/-- Stack bank obtained by emptying the specified ports and retaining all other contents. -/
def erased (ks : List K) (s : Stacks K) : Stacks K :=
  fun k => if k ∈ ks then [] else s k

theorem cleanup_runs (ks : List K) (s : Stacks K) (bound : ℕ)
    (h : ∀ i ∈ ks, (s i).length ≤ bound) :
    ∃ t ≤ ks.length * (bound + 1) + 1, (cleanup ks).Runs t s (erased ks s) := by
  induction ks generalizing s with
  | nil =>
    have he : erased [] s = s := by funext k; simp [erased]
    exact ⟨1, by simp, he.symm ▸ Routine.runs_ret s⟩
  | cons k ks ih =>
    obtain ⟨n, hn, tail⟩ := ih (Function.update s k []) (by
      intro j hj
      by_cases he : j = k
      · simp [he]
      · simpa [Function.update_of_ne he] using h j (List.mem_cons_of_mem k hj))
    have he : erased ks (Function.update s k []) = erased (k :: ks) s := by
      funext j
      by_cases h₁ : j = k <;> by_cases h₂ : j ∈ ks <;> simp [erased, h₁, h₂]
    rw [he] at tail
    have hk := h k (List.mem_cons_self ..)
    refine ⟨_, ?_, (clear_runs k s).followedBy tail⟩
    rw [List.length_cons, Nat.succ_mul]
    omega

end SliceArithmetic.CallClear

end VPVNP
end Computability
end OAI

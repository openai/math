import OAI.Computability.VPVNP.SliceArithmeticCallClear
import OAI.Computability.VPVNP.RAMTapeRoutinePorts

/-! # Reclaiming the private stacks at a team validator return

The finite control visits the private ports once in a fixed order. Each nonempty pop
discards one bit, each empty pop advances to the next port, and the last instruction
returns to the caller. The caller may choose the return label using a sign held in control.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamPrivateCleanup

open VPVNP.RAMTape VPVNP.SliceArithmetic.CallClear

variable {k : ℕ} {K L R : Type}

/-- The number of pops and the final return, including one empty pop at every private port. -/
def steps [Fintype K] (s : Stacks K) : ℕ := (∑ i, (s i).length) + Fintype.card K + 1

private theorem cleanup_exact [DecidableEq K] (ks : List K) (hd : ks.Nodup) (s : Stacks K) :
    (cleanup ks).Runs ((ks.map fun i => (s i).length).sum + ks.length + 1) s (erased ks s) := by
  induction ks generalizing s with
  | nil =>
    have h : erased [] s = s := by funext j; simp [erased]
    rw [h]
    exact Routine.runs_ret s
  | cons i ks ih =>
    obtain ⟨hi, hd⟩ := List.nodup_cons.mp hd
    have lengths : (ks.map fun j => ((Function.update s i []) j).length) =
        (ks.map fun j => (s j).length) := by
      apply List.map_congr_left
      intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      rw [Function.update_of_ne hji]
    have bank : erased ks (Function.update s i []) = erased (i :: ks) s := by
      funext j
      by_cases hji : j = i <;> by_cases hj : j ∈ ks <;> simp [erased, hji, hj]
    have tail := ih hd (Function.update s i [])
    rw [lengths, bank] at tail
    simpa only [cleanup, List.map_cons, List.sum_cons, List.length_cons, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using (clear_runs i s).followedBy tail

/-- Visit the private stacks in numerical order and return with all of them empty. -/
def routine (k : ℕ) : FiniteRoutine (Fin k) := cleanup (List.finRange k)

/-- Every private bit is popped exactly once, including on a completely empty bank. -/
theorem runs (s : Stacks (Fin k)) : (routine k).Runs (steps s) s (fun _ => []) := by
  have h := cleanup_exact (List.finRange k) (List.nodup_finRange k) s
  have hb : erased (List.finRange k) s = fun _ => [] := by funext i; simp [erased]
  simpa only [routine, steps, Fintype.card_fin, ← List.sum_toFinset _ (List.nodup_finRange k),
    List.toFinset_finRange, List.length_finRange, hb] using h

/-- The installed routine empties its private bank and preserves every other port. -/
theorem runs_onPorts [DecidableEq L] (ports : Fin k → L) (hp : Function.Injective ports)
    (base : Stacks L) :
    ((routine k).onPorts ports).Runs (steps (base ∘ ports)) base
      (installStacks ports base (fun _ => [])) := by
  have h := (routine k).runs_onPorts hp base (runs (base ∘ ports))
  rwa [installStacks_eq hp base (base ∘ ports) (fun _ => rfl)] at h

/-- Choose a fixed order for any finite set of private port names. -/
noncomputable def all (K : Type) [Fintype K] : FiniteRoutine K :=
  cleanup (List.ofFn (Fintype.equivFin K).symm)

/-- Cleanup of a finite named bank has the same exact cost as cleanup in numerical order. -/
theorem all_runs [Fintype K] [DecidableEq K] (s : Stacks K) :
    (all K).Runs (steps s) s (fun _ => []) := by
  let e := (Fintype.equivFin K).symm
  have h := cleanup_exact (List.ofFn e) (List.nodup_ofFn.mpr e.injective) s
  have hm (i : K) : i ∈ List.ofFn e := List.mem_ofFn.mpr (e.surjective i)
  have hb : erased (List.ofFn e) s = fun _ => [] := by funext i; simp [erased, hm]
  have hs := e.sum_comp (fun i => (s i).length)
  simpa only [all, e, steps, List.map_ofFn, List.sum_ofFn, Function.comp_apply, hs,
    List.length_ofFn, hb] using h

/-- An installed cleanup resumes at the caller's designated label in exactly its local time.
Using one label map per saved sign retains that sign through every pop and the return. -/
theorem all_linked [Fintype K] [DecidableEq K] [DecidableEq L] (target : StackCode L R)
    (ports : K → L) (hp : Function.Injective ports) (label : (all K).State → R)
    (resume : R) (base : Stacks L)
    (rows : ∀ q, target (label q) = ((all K).body.code q).rename ports (fun x => x.elim resume label)) :
    StackRuns target (steps (base ∘ ports)) (label (all K).body.entry) base resume
      (installStacks ports base (fun _ => [])) := by
  have h := (all_runs (base ∘ ports)).lift ports hp (fun x => x.elim resume label) base (by
    rintro (_ | q) hr
    · contradiction
    · exact rows q)
  rwa [installStacks_eq hp base (base ∘ ports) (fun _ => rfl)] at h

end TeamPrivateCleanup

end BorderVNP
end Computability
end OAI

import OAI.Computability.VPVNP.RAMTapeISAOperand

/-!
# Clearing a finite set of work stacks

An opcode may retain intermediate words at its return boundary. The caller
clears those stacks before the next instruction, using one pop per bit and
one empty-stack test per selected stack.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ISA

variable {r k : ℕ}

/-- Clear each listed port by popping its bits until the stack is empty, then return. -/
def clearList : List (Port r k) → FiniteRoutine (Port r k)
  | [] => .ret
  | k :: ks => (clearPort k).followedBy (clearList ks)

/-- Clearing a stack twice has the same result as clearing it once. -/
def cleared (ks : List (Port r k)) (s : Stacks (Port r k)) : Stacks (Port r k) := fun i => if i ∈ ks then [] else s i

theorem clearList_runs (ks : List (Port r k)) (s : Stacks (Port r k)) (bound : ℕ)
    (h : ∀ i ∈ ks, (s i).length ≤ bound) :
    ∃ n ≤ ks.length * (bound + 1) + 1, (clearList ks).Runs n s (cleared ks s) := by
  induction ks generalizing s with
  | nil =>
    have he : cleared [] s = s := by funext i; simp [cleared]
    exact ⟨1, by simp, he.symm ▸ Routine.runs_ret s⟩
  | cons k ks ih =>
    obtain ⟨t, ht, run⟩ := ih (Function.update s k []) (by
      intro i hi
      by_cases he : i = k
      · simp [he]
      · simpa [Function.update_of_ne he] using h i (List.mem_cons_of_mem _ hi))
    have he : cleared ks (Function.update s k []) = cleared (k :: ks) s := by
      funext i
      by_cases hk : i = k <;> by_cases hi : i ∈ ks <;> simp [cleared, hk, hi]
    rw [he] at run
    refine ⟨(s k).length + 1 + t, ?_, (clearPort_runs k s).followedBy run⟩
    have hh := h k (by simp)
    simp only [List.length_cons, Nat.succ_mul]
    omega

end RAMTape.ISA

end VPVNP
end Computability
end OAI

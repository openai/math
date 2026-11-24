import OAI.Computability.VPVNP.PairSimulationLeafLoadedBank

/-!
# The pending DFS stack after leaf initialization

The descriptors still to visit lie strictly below the scratch boundary.
Loading the virtual validator only changes words in its occupied stack
intervals, all of which start at or above that boundary. Restricting the
resulting memory to the scratch region gives the initialized leaf bank.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafIncidentBank

open BurstRAM RAMTape StackMachine
open scoped Fin.CommRing

variable {K : Type} {w : ℕ}

/-- A cell outside every occupied interval retains its previous word. -/
theorem memory_outside (L : Layout K w) (s : Stacks K) (old : Word w → Word w) (a : Word w)
    (outside : ∀ j, a.val < L.base j ∨ L.base j+(s j).length ≤ a.val) :
    LeafLoadedBank.memory L s old a = old a := by
  have empty : ¬ ∃ j, LeafLoadedBank.occupies L s a j := by
    rintro ⟨j, lo, hi⟩
    rcases outside j with below | beyond <;> omega
  rw [LeafLoadedBank.memory, LeafLoadedBank.readCell, dite_eq_right empty]
  rfl

/-- Installing the leaf bank preserves all pending DFS descriptors and
updates scratch by precisely the bank's occupied words. -/
theorem initialized_scratch (L : Layout K w) (s : Stacks K) {old mem : Word w → Word w}
    {endAddr top : ℕ} {pending : List (Word w)} (loaded : mem = LeafLoadedBank.memory L s old)
    (above : ∀ j, endAddr ≤ L.base j) (htop : top+pending.length = endAddr)
    (rep : DFS.Represents old top pending) :
    DFS.Represents mem top pending ∧
      DFS.scratch endAddr mem = LeafLoadedBank.scratch L s (DFS.scratch endAddr old) := by
  subst mem
  refine ⟨⟨rep.1, ?_⟩, LeafLoadedBank.scratch_memory L s endAddr old⟩
  intro i
  apply (memory_outside L s old _ ?_).trans (rep.2 i)
  intro j
  apply Or.inl
  change ((top+i.val : ℕ) : Word w).val < L.base j
  have pos := i.isLt
  have fit := rep.1
  rw [Fin.val_cast_of_lt (by omega)]
  have hj := above j
  omega

end PairSimulation.LeafIncidentBank

end VPVNP
end Computability
end OAI

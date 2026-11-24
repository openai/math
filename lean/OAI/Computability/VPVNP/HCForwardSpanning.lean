import OAI.Computability.VPVNP.HCForward
import OAI.Computability.VPVNP.HCGadgetSpanning

/-! The assignment traversal connects all track and clause vertices in one directed cycle. -/

namespace OAI
namespace Computability
namespace VPVNP

namespace HCGadget

open Equiv.Perm

variable {k h c : ℕ} (occ : Fin h → Fin k × Fin c × Bool) (x : Fin k → Bool) (hx : Exact occ x)

private theorem same_of_step {a b : Vertex k h c} (e : nextVertex occ x hx a = b) :
    (cycleOfAssignment occ x hx).SameCycle a b := by
  change cycleOfAssignment occ x hx a = b at e
  rw [← e]
  exact (SameCycle.refl _ _).apply_right

theorem cycleOfAssignment_buffers (i : Fin k) (j : Fin (h+1)) :
    (cycleOfAssignment occ x hx).SameCycle (prevPort i j) (.buffer i j) ∧
      (cycleOfAssignment occ x hx).SameCycle (.buffer i j) (nextPort i j) := by
  cases hi : x i with
  | false =>
    refine ⟨(same_of_step occ x hx ?_).symm,
      (same_of_step occ x hx (nextVertex_nextPort occ x hx hi j)).symm⟩
    simp [nextVertex, hi]
  | true =>
    refine ⟨same_of_step occ x hx (nextVertex_prevPort occ x hx hi j), same_of_step occ x hx ?_⟩
    simp [nextVertex, hi]

theorem cycleOfAssignment_slots (i : Fin k) (j : Fin h) :
    (cycleOfAssignment occ x hx).SameCycle (.port i j false) (.port i j true) := by
  have cross : (cycleOfAssignment occ x hx).SameCycle (.port i j (!x i)) (.port i j (x i)) := by
    by_cases ha : (occ j).1 = i ∧ (occ j).2.2 = x i
    · have hin : nextVertex occ x hx (.port i j (!x i)) = .clause (occ j).2.1 := by
        rw [nextVertex_ingress, ite_eq_left ha]
      exact (same_of_step occ x hx hin).trans (same_of_step occ x hx (nextVertex_clause_of_active occ x hx ha))
    · exact same_of_step occ x hx (by rw [nextVertex_ingress, ite_eq_right ha])
  cases hi : x i
  · simpa [hi] using cross.symm
  · simpa [hi] using cross

theorem cycleOfAssignment_enter (i : Fin k) :
    ∃ b, (cycleOfAssignment occ x hx).SameCycle (.sep i) (.endpoint i b) :=
  ⟨!x i, same_of_step occ x hx rfl⟩

theorem cycleOfAssignment_exit (i : Fin k) :
    ∃ b, (cycleOfAssignment occ x hx).SameCycle (.endpoint i b) (.sep (finRotate k i)) :=
  ⟨x i, same_of_step occ x hx (by simp [nextVertex])⟩

theorem cycleOfAssignment_clauses (a : Fin c) :
    ∃ i j b, (cycleOfAssignment occ x hx).SameCycle (.port i j b) (.clause a) := by
  let j := chosen occ x hx a
  have hc := chosen_spec occ x hx a
  refine ⟨(occ j).1, j, !x (occ j).1, same_of_step occ x hx ?_⟩
  rw [nextVertex_ingress, ite_eq_left ⟨rfl, hc.2.symm⟩, hc.1]

/-- Every exact-one assignment yields a spanning directed cycle using allowed arcs. -/
theorem cycleOfAssignment_spanning (hk : 0 < k) :
    (cycleOfAssignment occ x hx).IsCycleOn Set.univ :=
  isCycleOn_of_track_connections _ hk (cycleOfAssignment_buffers occ x hx)
    (cycleOfAssignment_slots occ x hx) (cycleOfAssignment_enter occ x hx)
    (cycleOfAssignment_exit occ x hx) (cycleOfAssignment_clauses occ x hx)

end HCGadget

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.RAMTapeSortRowCompare

/-!
# Dispatching and closing a comparison row

The public local-stride bit selects the corresponding row pass. The
private partner cursor is emptied when that pass returns.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortRow

theorem program_of_local {s m : Stacks Port} {t : ℕ} (hflag : s .localFlag = [true])
    (h : localPass.Runs t (Function.update s .localFlag []) m) :
    program.Runs (t+1+(2*(m .partner).length+1)) s (Function.update m .partner []) := by
  apply FiniteRoutine.Runs.followedBy (a := _) (b := clearPartner) (s := s) (t := m)
  · exact Routine.runs_popCase_true Port.localFlag (Routine.halt false) crossPass.body localPass.body hflag h
  · exact clearPartner_runs m

theorem program_of_cross {s m : Stacks Port} {t : ℕ} (hflag : s .localFlag = [false])
    (h : crossPass.Runs t (Function.update s .localFlag []) m) :
    program.Runs (t+1+(2*(m .partner).length+1)) s (Function.update m .partner []) := by
  apply FiniteRoutine.Runs.followedBy (a := _) (b := clearPartner) (s := s) (t := m)
  · exact Routine.runs_popCase_false Port.localFlag (Routine.halt false) crossPass.body localPass.body hflag h
  · exact clearPartner_runs m

/-- One row visits at most two records of its block, verifies at most one
outgoing field, and selects one of its two operands. -/
theorem rowCost_le {i j B w : ℕ} (hi : i ≤ B) (hj : j ≤ B) :
    (5*i+2+SortGather.cost i w) + (50*w+18) + (5*j+2+SortGather.cost j w) +
      (65*w+20) + 1 + (2*B+1) ≤ 4096*(B+1)*(w+1) := by
  have hiw := Nat.mul_le_mul_right (40*w+12) hi
  have hjw := Nat.mul_le_mul_right (40*w+12) hj
  unfold SortGather.cost
  ring_nf at hiw hjw ⊢
  omega

end RAMTape.SortRow

end VPVNP
end Computability
end OAI

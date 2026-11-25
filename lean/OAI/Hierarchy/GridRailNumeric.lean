import OAI.Hierarchy.GridLensSites
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Start addresses and strides of actual coordinate lines -/

namespace Hierarchy.GridLens
open scoped BigOperators

variable {k n : ℕ}

/-- Read the `j`th base-`g` digit of a cell ordinal. The first axis is least significant. -/
theorem ordinal_digit (x : Fin k → Fin (n+1)) (j : Fin k) :
    (finFunctionFinEquiv x).val / (n+1)^j.val % (n+1) = (x j).val :=
  congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply x) j)

/-- Erasing the longitudinal digit and inserting the sweep coordinate recovers the exact cell. -/
theorem ordinal_onRail (x : Fin k → Fin (n+1)) (j : Fin k) (t : Fin (n+1)) :
    (finFunctionFinEquiv (cellOnRail j x t)).val =
      ((finFunctionFinEquiv x).val - ((finFunctionFinEquiv x).val / (n+1)^j.val % (n+1)) * (n+1)^j.val) +
        t.val * (n+1)^j.val := by
  rw [ordinal_digit]
  have split (y : Fin k → Fin (n+1)) : (finFunctionFinEquiv y).val =
      (y j).val * (n+1)^j.val + ∑ i ∈ Finset.univ.erase j, (y i).val * (n+1)^i.val := by
    rw [finFunctionFinEquiv_apply]
    exact (Finset.add_sum_erase Finset.univ (fun i : Fin k => (y i).val * (n+1)^i.val) (Finset.mem_univ j)).symm
  have rest : (∑ i ∈ Finset.univ.erase j, ((cellOnRail j x t) i).val * (n+1)^i.val) =
      ∑ i ∈ Finset.univ.erase j, (x i).val * (n+1)^i.val := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [cellOnRail_off x t (Finset.mem_erase.mp hi).1]
  rw [split (cellOnRail j x t), split x, cellOnRail_axis, rest]
  omega

/-- The cell/direction counter uses the dense address `cell*k + j`. -/
theorem bank_onRail (x : Fin k → Fin (n+1)) (j : Fin k) (t : Fin (n+1)) :
    (finFunctionFinEquiv (cellOnRail j x t)).val*k + j.val =
      ((finFunctionFinEquiv x).val - ((finFunctionFinEquiv x).val / (n+1)^j.val % (n+1))*(n+1)^j.val)*k +
        j.val + t.val*((n+1)^j.val*k) := by
  rw [ordinal_onRail]
  ring

end Hierarchy.GridLens

end OAI

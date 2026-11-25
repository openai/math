import OAI.Hierarchy.DescentPublicStepKinds
import Mathlib.Tactic

namespace OAI
/-! # A reset occupies the final position of its public period -/
namespace Hierarchy.DescentSixParty.Chronology

theorem reset_slot_index (rounds epochs i : ℕ) (hit : ((kindCalendar rounds epochs).drop i).head?=some true) :
    i%(rounds+1)=rounds :=by
  rw [List.head?_drop] at hit
  induction epochs generalizing i with
  | zero=>simp [kindCalendar] at hit
  | succ e ih=>
    rw [kindCalendar,List.replicate_succ,List.flatten_cons] at hit
    have len : (kindPeriod rounds).length=rounds+1:=by simp [kindPeriod]
    by_cases first:i<rounds+1
    · rw [List.getElem?_append_left (by simpa only [len] using first)] at hit
      rw [Nat.mod_eq_of_lt first]
      by_contra neq
      have small:i<rounds:=by omega
      unfold kindPeriod at hit
      rw [List.getElem?_append_left (by simpa using small),List.getElem?_replicate,ite_eq_left small] at hit
      cases hit
    · have passed : rounds+1 ≤ i :=Nat.le_of_not_gt first
      rw [List.getElem?_append_right (by simpa only [len] using passed),len] at hit
      have rest:=ih (i-(rounds+1)) hit
      have total:(i-(rounds+1))+(rounds+1)=i:=Nat.sub_add_cancel passed
      calc i%(rounds+1)=((i-(rounds+1))+(rounds+1))%(rounds+1):=congrArg (·%(rounds+1)) total.symm
           _=rounds:=by simpa using rest

end Hierarchy.DescentSixParty.Chronology

end OAI

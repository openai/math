import OAI.Hierarchy.DescentRegisterTimelineRoom

namespace OAI
/-! # Price of an offered event from the already admitted part of the timeline -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook Filter
noncomputable section

theorem candidate_floor {w h A B i n : ℕ} {Cut : ℕ→Type*}
    (issue : ∀j,Cut j→Position→Move w→Prop) (initial : Position) (next : ℕ)
    (positive : 0<h) (before : i<n) (count : n≤2^(A*h)) (header : initial.floor≤2^(B*h))
    (earlier : ∀j < i,span issue initial j≤2^(B*h))
    (offered : next-(position issue initial i).floor≤2^(B*h)) :
    next<2^((A+B+2)*h) :=by
  let interval (j : ℕ) := if j=i then next-(position issue initial i).floor else span issue initial j
  have same (j : ℕ) (bound : j ≤ i) : floor initial.floor interval j=floor initial.floor (span issue initial) j:=by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [floor_succ,floor_succ,ih (by omega)]
      simp only [interval,ite_eq_right (show j≠i by omega)]
  have bigger : next≤floor initial.floor interval (i+1):=by
    rw [floor_succ,same i (le_refl _),←position_floor]
    simp only [interval,ite_eq_left rfl]
    omega
  apply lt_of_le_of_lt bigger (within_word positive interval header (before.trans_le count) ?_)
  intro j hj
  by_cases last : j=i
  · simpa only [interval,ite_eq_left last] using offered
  · simpa only [interval,ite_eq_right last] using earlier j (by omega)

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI

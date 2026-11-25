import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin

/-! # Stable gathering of selected binary coordinate positions

The mask is given in increasing bit position. Positions with a true mask bit
fill the low part of the gathered address, preserving their order, and the
remaining positions fill the high part in their original order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GatherMask

def order (mask : List Bool) : List (Fin mask.length) :=
  (List.finRange mask.length).filter mask.get ++
    (List.finRange mask.length).filter (fun i => !(mask.get i))

theorem order_perm (mask : List Bool) : (order mask).Perm (List.finRange mask.length) :=
  List.filter_append_perm _ _

@[simp] theorem length_order (mask : List Bool) : (order mask).length = mask.length :=
  (order_perm mask).length_eq.trans List.length_finRange

/-- Map an original bit position to its position in the gathered address. -/
def perm (mask : List Bool) : Equiv.Perm (Fin mask.length) :=
  (List.Nodup.getEquivOfForallMemList (order mask)
    ((order_perm mask).nodup_iff.mpr (List.nodup_finRange _))
    (fun i => (order_perm mask).mem_iff.mpr (List.mem_finRange i))).symm.trans
    (finCongr (length_order mask))

theorem forward_idxOf (mask : List Bool) (i : Fin mask.length) :
    (perm mask i).val = (order mask).idxOf i := rfl

theorem backward_get (mask : List Bool) (i : Fin mask.length) :
    (perm mask).symm i = (order mask).get (i.cast (length_order mask).symm) := rfl

/-- Inverse positions can be emitted directly by mapping the two ordered lists. -/
theorem inverse_list {α : Type*} (mask : List Bool) (f : Fin mask.length → α) :
    (List.ofFn fun i => f ((perm mask).symm i)) = (order mask).map f := by
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    simp only [List.getElem_ofFn,List.getElem_map,backward_get]
    rfl

private theorem mask_eq (m : List Bool) : (List.finRange m.length).map m.get = m := by
  rw [← List.ofFn_eq_map, List.ofFn_get]

private theorem true_count {m : List Bool} (l : List (Fin m.length)) :
    (l.filter m.get).length = (l.map m.get).count true := by
  simp [List.count_eq_countP,List.countP_map,← List.countP_eq_length_filter,Function.comp_def]

  rfl

private theorem false_count {m : List Bool} (l : List (Fin m.length)) :
    (l.filter (fun i => !(m.get i))).length = (l.map m.get).count false := by
  simp [List.count_eq_countP,List.countP_map,← List.countP_eq_length_filter,Function.comp_def]

private theorem filter_rank {n : ℕ} (p : Fin n → Bool) (i : Fin n) (hp : p i = true) :
    ((List.finRange n).filter p).idxOf i = (((List.finRange n).take i.val).filter p).length := by
  let l := List.finRange n
  have hi : i.val < l.length := by simp [l]
  have he : l[i.val] = i := by simp [l]
  have no : i ∉ (l.take i.val).filter p := by
    intro h
    have h' := (List.mem_take_iff_idxOf_lt (List.mem_finRange i)).mp (List.mem_filter.mp h).1
    simp at h'
  have split : l = l.take i.val ++ (i :: l.drop (i.val+1)) := by
    conv_lhs => rw [← List.take_append_drop i.val l, List.drop_eq_getElem_cons hi,he]
  change (l.filter p).idxOf i = _
  conv_lhs => rw [split, List.filter_append, List.filter_cons_of_pos hp,
    List.idxOf_append_of_notMem no, List.idxOf_cons_self, Nat.add_zero]

theorem forward_rank (mask : List Bool) (i : Fin mask.length) :
    (perm mask i).val = if mask.get i then (mask.take i.val).count true
      else mask.count true + (mask.take i.val).count false := by
  rw [forward_idxOf,order]
  cases h : mask.get i with
  | true =>
    rw [List.idxOf_append_of_mem (List.mem_filter.mpr ⟨List.mem_finRange i,h⟩),
      filter_rank _ i h, true_count, List.map_take,mask_eq]
    rfl
  | false =>
    have no : i ∉ (List.finRange mask.length).filter mask.get := by simp only [List.mem_filter,h,Bool.false_eq_true,and_false,not_false_eq_true]
    rw [List.idxOf_append_of_notMem no, filter_rank _ i (by simp only [h,Bool.not_false]),
      false_count,true_count,List.map_take,mask_eq]
    rfl

theorem low_iff (mask : List Bool) (i : Fin mask.length) :
    (perm mask i).val < mask.count true ↔ mask.get i = true := by
  cases h : mask.get i with
  | false => rw [forward_rank,h]; simp
  | true =>
    have mem : i ∈ (List.finRange mask.length).filter mask.get :=
      List.mem_filter.mpr ⟨List.mem_finRange i,h⟩
    have bound := List.idxOf_lt_length_of_mem mem
    rw [true_count,mask_eq] at bound
    simpa only [Bool.true_eq, iff_true, forward_idxOf,order,List.idxOf_append_of_mem mem] using bound

end PhysicalWalsh.GatherMask

end NearSquareRoot
end Computability
end OAI

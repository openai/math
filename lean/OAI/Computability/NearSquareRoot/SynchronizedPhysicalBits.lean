import OAI.Computability.NearSquareRoot.SynchronizedBoxLayout
import OAI.Computability.NearSquareRoot.SynchronizedAddress

/-! # Selected Walsh bits in the physical tape address

The synchronized local slots use the high bit in the first axis of each
participating block. The positions here are ordinary least-significant-bit
offsets in the linear stream address.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxFin

open Finset SynchronizedBlocks
variable {box : List (ℕ × ℕ)} {k l : ℕ} (hb : BoxShape.Valid k l box)

theorem offset_eq (i : Fin box.length) :
    offset i = ∑ j ∈ Iio i, (box.get j).1 := by
  unfold offset
  symm
  exact sum_bij' (fun (j : Fin box.length) hj => (⟨j.val, show j < i from mem_Iio.mp hj⟩ : Fin i.val))
    (fun j _ => Fin.castLE i.isLt.le j)
    (fun _ _ => mem_univ _) (fun j _ => mem_Iio.mpr j.isLt)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

private theorem offset_add_width (i : Fin box.length) :
    offset i + (box.get i).1 = ∑ j ∈ insert i (Iio i), (box.get j).1 := by
  rw [sum_insert (by simp), offset_eq, Nat.add_comm]

include hb in
theorem offset_add_width_le (i : Fin box.length) : offset i + (box.get i).1 ≤ k := by
  rw [offset_add_width]
  exact (sum_le_sum_of_subset (Finset.subset_univ _)).trans_eq
    ((Fin.sum_univ_fun_getElem box Prod.fst).trans hb.widthSum)

theorem offset_add_width_le_next {i j : Fin box.length} (hij : i < j) :
    offset i + (box.get i).1 ≤ offset j := by
  rw [offset_add_width, offset_eq]
  apply sum_le_sum_of_subset
  intro t ht
  rcases (Finset.mem_insert.mp ht) with rfl | hti
  · exact mem_Iio.mpr hij
  · exact mem_Iio.mpr ((mem_Iio.mp hti).trans hij)

/-- The designated physical position of a block in the original binary address. -/
def selectedPosition (j : Fin (box.length / 4)) : Fin k :=
  let i := axis j (firstAxis j)
  ⟨offset i + ((box.get i).1 - 1), by
    have := offset_add_width_le hb i
    have := (hb.axisBounds _ (List.get_mem box i)).1
    omega⟩

theorem selectedPosition_strictMono : StrictMono (selectedPosition hb) := by
  intro j j' hj
  have hi : axis j (firstAxis j) < axis j' (firstAxis j') := by
    change 4 * j.val + 0 < 4 * j'.val + 0
    omega
  have hlt := offset_add_width_le_next (box := box) hi
  have h₁ := (hb.axisBounds _ (List.get_mem box (axis j (firstAxis j)))).1
  change offset _ + (_-1) < offset _ + (_-1)
  omega

variable [∀ i, NeZero (modulus box i)]

/-- A bit in any local axis field equals its corresponding bit in the linear tape address. -/
theorem testBit_field (x : (i : Fin box.length) → Axis (modulus box i) (padding box i)) (i : Fin box.length)
    {q : ℕ} (hq : q < (box.get i).1) :
    (field hb i (x i)).val.testBit q = (recordIndex hb x).val.testBit (offset i + q) := by
  have h := extract_field hb (recordIndex hb x) i
  rw [Equiv.symm_apply_apply] at h
  rw [h, Nat.testBit_mod_two_pow, decide_eq_true hq, Bool.true_and, Nat.testBit_div_two_pow,
    Nat.add_comm]

/-- The mathematical bit in the synchronized Walsh matrix is exactly the bit
read from its physical slot in the lexicographic tape array. -/
theorem boxBits_physical (hd : 4 ≤ box.length) (x : (i : Fin box.length) → Axis (modulus box i) (padding box i))
    (j : Fin (box.length/4)) :
    decide (((bitLayout (modulus box) (padding box) (fun i => (box.get i).1)
      (fun i => (hb.axisBounds _ (List.get_mem _ i)).1)
      (fun i => Nat.add_sub_of_le (hb.axisBounds _ (List.get_mem _ i)).2.2.2) j) (regroup hd _ x j)).1.val = 1) =
      (recordIndex hb x).val.testBit (selectedPosition hb j).val := by
  let i := axis j (firstAxis j)
  have hw := (hb.axisBounds _ (List.get_mem box i)).1
  let q := (box.get i).1 - 1
  have hq : q < (box.get i).1 := Nat.sub_lt hw (by decide : 0 < 1)
  change decide ((field hb i (x i)).val / 2^q = 1) = (recordIndex hb x).val.testBit (offset i + q)
  rw [← testBit_field hb x i hq, Nat.testBit_eq_decide_div_mod_eq]
  have hlt : (field hb i (x i)).val / 2^q < 2 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).2
    have h := (field hb i (x i)).isLt
    exact h.trans_eq (show 2^(box.get i).1 = 2 * 2^q by
      rw [show (box.get i).1 = q+1 from (Nat.sub_add_cancel hw).symm, Nat.pow_succ'])
  rw [Nat.mod_eq_of_lt hlt]

end BoxFin

end NearSquareRoot
end Computability
end OAI

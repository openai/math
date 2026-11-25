import OAI.Computability.NearSquareRoot.SynchronizedBoxPlanProgram

/-! # Depth of the generated physical box word -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Staff IntegerMultiplication.Strip
open SynchronizedLayers.ScheduleProgram SynchronizedBlocks

private theorem orientRows_length {X : Type} (b : Bool) (xs : List X) :
    (orientRows (b,xs)).length = xs.length := by
  cases b <;> simp [orientRows, polyPush]

private theorem plan_length {X : Type} (kind : X → SynchronizedLayers.Kind)
    (w : List (List X)) (d : Tally) :
    (plan kind (w,d)).length = 3 * d.length := by
  rw [plan, List.length_flatMap]
  change ((Iter.lineup d).map (fun _ => 3)).sum = 3 * d.length
  simp [List.map_const', List.sum_replicate, Nat.mul_comm]

private theorem boxPlan_length (u : Tally) : (boxPlan u).length = 3 * boxDepth u.length := by
  unfold boxPlan
  rw [plan_length, tally_length]

theorem directedPlan_length (inv : Bool) (k : ℕ) :
    (directedPlan (inv,tally k)).length = 3 * boxDepth k := by
  unfold directedPlan
  rw [orientRows_length, boxPlan_length, tally_length]

/-- The literal tape rows are exactly the schedule on the local mathematical block words. -/
theorem boxPlan_eq (k : ℕ) :
    boxPlan (tally k) = plan slotKind (List.ofFn (fun j : Fin ((CoprimeBox.box k).length/4) =>
      localSlots (block (List.ofFn (fun i : Fin (count j) => tally
        (paddedLog (BoxFin.modulus (CoprimeBox.box k) (axis j i))))))), tally (boxDepth k)) := by
  unfold boxPlan
  rw [tally_length, boxWords_eq, List.map_ofFn]
  congr 1
  refine Prod.ext ?_ rfl
  apply congrArg List.ofFn
  funext j
  exact congrArg localSlots (block_eq_typed _).symm

theorem local_length_le {k : ℕ} (h : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k))
    (j : Fin ((CoprimeBox.box k).length/4)) :
    (localSlots (block (List.ofFn fun i : Fin (count j) =>
      tally (paddedLog (BoxFin.modulus (CoprimeBox.box k) (axis j i)))))).length ≤ boxDepth k := by
  let a := BoxFin.modulus (CoprimeBox.box k)
  let K := fun i : Fin (count j) => paddedLog (a (axis j i))
  have hk (i : Fin (count j)) : K i ≤ BoxScale.width k + 1 := by
    let t := axis j i
    have hb := h.axisBounds _ (List.get_mem (CoprimeBox.box k) t)
    have hm : Nat.clog 2 (a t) ≤ ((CoprimeBox.box k).get t).1 :=
      Nat.clog_le_of_le_pow hb.2.2.2
    exact (paddedLog_le _).trans (Nat.add_le_add_right (hm.trans hb.2.1) 1)
  apply (localSlots_length_le _).trans
  rw [block_eq_typed, List.length_map]
  apply Nat.mul_le_mul_left 8
  exact (typed_length_le K hk).trans (Nat.mul_le_mul_right _ (count_bounds j).2)

end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI

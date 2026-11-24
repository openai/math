import OAI.Computability.VPVNP.PairSimulationLeafSortWalk
import OAI.Computability.VPVNP.RAMTapeSortScheduleFields

/-!
# Identifying the native sort-field stream with the local cursor decoder
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafSortFields

open CursorNetwork CursorRouting RAMLayout RAMTape.SortSchedule

variable {D w H : ℕ} [NeZero D]

theorem previous_zero : ((finRotate D).symm (0 : Fin D)).val = D-1 := by
  cases D with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    have he : (finRotate (n+1)).symm 0 = Fin.last n :=
      (finRotate (n+1)).symm_apply_eq.mpr (finRotate_last ..).symm
    simp [he]

/-- A native sorting-field read addresses exactly the selected half on
every bit. The current cursor reads bit zero and the predecessor cursor
reads bit D−1 of the layer mask. -/
theorem field_eq (l : Layer D) (recv : Bool) (v : Site D) (buf : Buffers D H w) :
    field l recv buf = List.ofFn fun j : Fin (blockBits H w) =>
      incidentBuffer (0,v) buf (offset D H w (.inr (l,if recv then 1 else 0,j))) := by
  apply congrArg List.ofFn
  funext j
  have addr : (ramFieldOffset D H w ⟨.inr l,j⟩).val = arcStart l H w+j.val := ramFieldOffset_sort l j
  cases recv <;>
    simp only [port,side,Bool.false_eq_true,↓reduceIte,
      incidentBuffer,decodeIncident,Function.comp_apply,Equiv.symm_apply_apply,decodeSlot,
      Fin.val_zero,readBuffer,systemMask,Nat.testBit_two_pow,previous_zero]
  all_goals (congr 2; exact addr.symm)

theorem stream_eq_fields (v : Site D) (buf : Buffers D H w) :
    stream buf 0 (layerCount D) (by simp) =
      (List.range (layerCount D)).flatMap (fieldPair (incidentBuffer (0,v) buf)) := by
  rw [stream,List.flatMap_def]
  apply congrArg List.flatten
  apply List.ext_getElem (by simp)
  intro i hi hj
  have h : i < layerCount D := by simpa using hi
  simp [fieldPair,block,field_eq _ false v buf,field_eq _ true v buf,h]

end PairSimulation.LeafSortFields

end VPVNP
end Computability
end OAI

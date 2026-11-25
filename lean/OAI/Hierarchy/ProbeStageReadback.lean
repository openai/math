import OAI.Hierarchy.ProbeStageNumbering
import OAI.Hierarchy.ProbeStageNativeCorrect

namespace OAI
/-! # Reading every routed tile from its final physical stage bank -/

namespace Hierarchy.ProbeStage.Native
open ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Fin.CommRing
noncomputable section

/-- The numbered stage agrees at the exact native stage ordinal with the
routed tile list consumed by the payload and sampler proofs. -/
theorem stageMatching_route {h d : ℕ} (π : Equiv.Perm (Fin (2^h))) (s : Fin (2*rounds d+1)) :
    (advisedRoute h d π).layers[s.val]?=some (layer (stageMatching π s).tiles) := by
  let q := rounds d
  let p := history h d π
  let a := (formatAdvice h d).row
  let enterList := (List.range q).map (fun j => Matching.entering (radix_pos h d) a (p j))
  let leaveList := (List.range q).map (fun j => Matching.leaving (radix_pos h d) a (p j))
  have en : enterList.length=q := by simp [enterList]
  have le : leaveList.length=q := by simp [leaveList]
  have takeEnter (i : ℕ) (hi : i<q) : enterList[i]?=some (Matching.entering (radix_pos h d) a (p i)) := by
    unfold enterList
    rw [List.getElem?_map,List.getElem?_range hi]; rfl
  have takeLeave (i : ℕ) (hi : i<q) : leaveList[i]?=some (Matching.leaving (radix_pos h d) a (p i)) := by
    unfold leaveList
    rw [List.getElem?_map,List.getElem?_range hi]; rfl
  rw [advised_history]
  change ((enterList++[layer (p q).tiles])++leaveList.reverse)[s.val]?=_
  by_cases left : s.val<q
  · rw [List.getElem?_append_left (by simp [en];omega),List.getElem?_append_left (by omega)]
    rw [takeEnter _ left,stageMatching,dite_eq_left left]; rfl
  by_cases middle : s.val=q
  · rw [List.getElem?_append_left (by simp [en];omega),List.getElem?_append_right (by omega),en,middle]
    rw [stageMatching,dite_eq_right left,dite_eq_left middle,Nat.sub_self]; rfl
  · rw [List.getElem?_append_right (by simp [en];omega)]
    have inLeave : s.val-(q+1)<leaveList.length := by rw [le];have range : s.val<2*q+1 := s.isLt;omega
    simp only [List.length_append,en,List.length_cons,List.length_nil,Nat.zero_add]
    rw [List.getElem?_reverse inLeave]
    have idx : leaveList.length-1-(s.val-(q+1))=2*q-s.val := by rw [le];omega
    rw [idx]
    have valid : 2*q-s.val<q := by omega
    rw [takeLeave _ valid,stageMatching,dite_eq_right left,dite_eq_right middle]; rfl

/-- The three consumed words are exactly the group number, input port
and output port of the indexed matching. -/
theorem stageBank_reads {h d : ℕ} (π : Equiv.Perm (Fin (2^h))) (input : Memory (wordBits h d copies))
    (done : After (d:=d) π input (rounds d)) (s : Fin (2*rounds d+1)) (c : Fin 3) :
    Resident (stageBank h d s c) (images h d input (rounds d))
      (fun r => fieldNumber (stageMatching π s) r c) := by
  let n := 2^h
  have cap := (height_extent h d).trans (extent_word h d copies).le
  by_cases left : s.val<rounds d
  · let j : Fin (rounds d) := ⟨s.val,left⟩
    rw [stageBank,ite_eq_left left,stageMatching,dite_eq_left left]
    apply Resident.of_cells _ _ _ le_rfl cap
    intro r
    have wrote := done.rows j j.isLt r (⟨c.val,by omega⟩:Fin 9)
    fin_cases c <;> exact wrote
  by_cases middle : s.val=rounds d
  · rw [stageBank,ite_eq_right left,ite_eq_left middle,stageMatching,dite_eq_right left,dite_eq_left middle]
    fin_cases c
    · exact done.parent.group
    · exact done.parent.source
    · exact done.parent.target
  · let j : Fin (rounds d) := ⟨2*rounds d-s.val,by omega⟩
    rw [stageBank,ite_eq_right left,ite_eq_right middle,stageMatching,dite_eq_right left,dite_eq_right middle]
    apply Resident.of_cells _ _ _ le_rfl cap
    intro r
    have wrote := done.rows j j.isLt r (⟨6+c.val,by omega⟩:Fin 9)
    fin_cases c <;> exact wrote

end
end Hierarchy.ProbeStage.Native

end OAI

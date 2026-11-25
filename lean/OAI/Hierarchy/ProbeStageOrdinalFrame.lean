import OAI.Hierarchy.ProbeStagePhysicalCommit
import OAI.Hierarchy.ProbeStagePhysicalStart
import OAI.Hierarchy.ProbeStageRecordContract

namespace OAI
/-! # The complete write frame of the allocator at one ordinal -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM
open scoped Fin.CommRing
noncomputable section

variable {h d : ℕ} (hd : 1≤d) (j : Fin (rounds d)) (i : Fin (2^h))

theorem start_frame (m : Memory (ramWidth h d)) (x : ℕ) (away : ¬MayWrite h d j.val i x) :
    atCommits j i m x=m x := by
  have temp (k : Fin 12) : x≠scratch h d j.val k := fun e => away (Or.inr (Or.inl ⟨k,e⟩))
  have rank : x≠rankAddr h d j.val 0 i := fun e => away (Or.inl ⟨0,e⟩)
  rw [atCommits,Record.left_prepared _ _ _ _ _ (temp 6) rank (temp 7) (scratch_fits j 7)]
  exact prepared_frame j i m x (fun _ => temp _)

private theorem count_writable (l : Bool) (b : Fin (groupBlocks h d j.val)) (c : Fin (radix h d)) :
    MayWrite h d j.val i (Cell.addr j.val (countTag hd j l b c)) := by
  cases l
  · exact Or.inr (Or.inr ⟨1,⟨_,count_offset hd j.isLt.le b c⟩,rfl⟩)
  · exact Or.inr (Or.inr ⟨0,⟨_,count_offset hd j.isLt.le b c⟩,rfl⟩)

include hd in
private theorem mask_writable (l : Bool) (b : Fin (groupBlocks h d j.val)) (r : MaskIndex (radix h d))
    (k : Fin (fieldChunks h)) : MayWrite h d j.val i (maskLocation h d j.val l b r k) := by
  let off : Fin (regionSize h d) := ⟨_,mask_offset hd j.isLt.le b r k⟩
  cases l
  · exact Or.inr (Or.inr ⟨3,off,by simp [off,maskLocation,maskArea,Nat.add_assoc]⟩)
  · exact Or.inr (Or.inr ⟨2,off,by simp [off,maskLocation,maskArea,Nat.add_assoc]⟩)

theorem outside_frame {l : Bool} {b : Fin (groupBlocks h d j.val)} {c : Fin (radix h d)} {rank : ℕ}
    {m : Memory (ramWidth h d)} (ready : Commit hd j i l b c rank m) (x : ℕ)
    (away : ¬MayWrite h d j.val i x) : RankUpdate.image (physicalSide j i l) m x=m x := by
  apply ready.frame
  · intro inside
    obtain ⟨tag,mem,rfl⟩ := List.mem_map.mp inside
    apply away
    have scratch_ok (k : Fin 12) : MayWrite h d j.val i (Cell.addr j.val (.temp k)) := Or.inr (Or.inl ⟨k,rfl⟩)
    simp only [coreTargets,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
    · exact scratch_ok 8
    · exact Or.inl ⟨roleRank l,rfl⟩
    · exact scratch_ok 9
    · exact count_writable hd j i l b c
    · exact scratch_ok 10
    · exact scratch_ok 11
  · intro r k e
    apply away
    rw [e]
    exact mask_writable hd j i l b r k

end
end Hierarchy.ProbeStage.Native

end OAI

import OAI.Hierarchy.ProbeStageProgram
import OAI.Hierarchy.ProbeStageDirectoryWords
import OAI.Hierarchy.ProbeStageRecordPrepare

namespace OAI
/-! # The six prepared words at a physical record ordinal -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM
open scoped Fin.CommRing
noncomputable section

variable {h d : ℕ} (j : Fin (rounds d)) (i : Fin (2^h))

def argumentAddr (q : Fin 3) := (blockBank h d copies j q).base+i.val

def preparedMemory (m : Memory (wordBits h d copies)) :=
  Record.writes (Record.prepare (recordAdvice h d j) (recordRow h d j i.val) (recordScratch h d j)) m

def dirInput : Fin 6 → Fin 3 := ![0,1,0,1,2,2]

def physicalLoad (k : Fin 6) : Record.Load :=
  ⟨scratch h d j ⟨k.val,by omega⟩,region h d j ⟨k.val,by omega⟩,argumentAddr j i (dirInput k)⟩

theorem physical_dirs :
    Record.dirs (recordAdvice h d j) (recordRow h d j i.val) (recordScratch h d j)=
      List.ofFn (physicalLoad j i) := rfl

theorem argument_low (k : Fin 3) (q : Fin 12) : argumentAddr j i k<scratch h d j q := by
  have cap := allocator_end h d copies j.val
  have off := Nat.mul_le_mul_right (2^h) (show k.val+1≤3 by omega)
  rw [Nat.succ_mul] at off
  have hi := i.isLt
  change allocatorBase h d copies j.val+k.val*2^h+i.val < bankBase h d copies j.val 14+q.val
  omega

theorem chosen_low (q : Fin 12) : (recordRow h d j i.val).chosen<scratch h d j q := by
  have hi := i.isLt.trans_le (height_extent h d)
  have before := separate h d copies j.val 0 14 (by decide)
  change bankBase h d copies j.val 0+i.val<bankBase h d copies j.val 14+q.val
  omega

theorem scratch_fits (k : Fin 12) : scratch h d j k < 2^wordBits h d copies := by
  have room := region_word (h:=h) j.isLt (0:Fin 16) (i:=0) (by unfold regionSize extent;positivity)
  exact (scratch_separate h d j.val k 0).trans (by simpa using room)

include j in
theorem regionSize_fits : regionSize h d < 2^wordBits h d copies := by
  have end_ := region_end h d j.val 0
  have bound := (output_end h d copies j.val).trans_lt ((phase_in_heap j.isLt).trans_lt (heap_room ..))
  omega

theorem scratch_ne {p q : Fin 12} (ne : p≠q) : scratch h d j p≠scratch h d j q := by
  intro e
  exact ne (Fin.ext (Nat.add_left_cancel e))

theorem prepared_frame (m : Memory (wordBits h d copies)) (a : ℕ)
    (away : ∀ k : Fin 6, a≠scratch h d j ⟨k.val,by omega⟩) :
    preparedMemory j i m a=m a := by
  apply Record.writes_frame
  rw [Record.prepare_eq,physical_dirs,List.map_ofFn]
  intro z mem
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp mem
  exact away k

theorem prepared_region (m : Memory (wordBits h d copies)) (k : Fin 16) (o : ℕ) :
    preparedMemory j i m (region h d j k+o)=m (region h d j k+o) :=
  prepared_frame j i m _ fun a => by have := scratch_separate h d j.val ⟨a.val,by omega⟩ k;omega

/-- The fixed three words emitted by the endpoint pass, on this ordinal. -/
def argumentValue (left right : Fin (groupBlocks h d j.val)) (r : MaskIndex (radix h d)) :
    Fin 3 → ℕ := ![left.val,right.val,rowCode r]

/-- The denominator-free pointer or offset returned by each immutable table. -/
def loadedValue (left right : Fin (groupBlocks h d j.val)) (r : MaskIndex (radix h d)) : Fin 6 → ℕ :=
  ![region h d j 12+left.val*radix h d,region h d j 13+right.val*radix h d,
    region h d j 14+left.val*((radix h d)^4*fieldChunks h),
    region h d j 15+right.val*((radix h d)^4*fieldChunks h),
    rowCode r*fieldChunks h,rowCode r*stringLength h]

theorem prepared_word (hd : 1≤d) (m : Memory (wordBits h d copies))
    (rom : immutable h d _ j m) (left right : Fin (groupBlocks h d j.val)) (r : MaskIndex (radix h d))
    (ids : ∀ q,m (argumentAddr j i q)=(argumentValue j left right r q : Word _)) (k : Fin 6) :
    preparedMemory j i m (scratch h d j ⟨k.val,by omega⟩)=(loadedValue j left right r k : Word _) := by
  have bounds := region_room (h:=h) hd j.isLt.le
  have small (q : Fin 3) : argumentValue j left right r q<regionSize h d := by
    fin_cases q
    · exact left.isLt.trans_le bounds.1
    · exact right.isLt.trans_le bounds.1
    · exact (rowCode_lt r).trans_le bounds.2.2.1
  have loc (q : Fin 6) : (physicalLoad j i q).addr m =
      region h d j ⟨q.val,by omega⟩+argumentValue j left right r (dirInput q) := by
    change ((region h d j ⟨q.val,by omega⟩ : Word _)+m ((argumentAddr j i (dirInput q) : Word (wordBits h d copies))).val).val=_
    rw [Fin.val_cast_of_lt ((argument_low j i _ 0).trans (scratch_fits j 0)),ids,add_word (region_word j.isLt _ (small _))]
  have apart : ∀ u∈List.ofFn (physicalLoad j i), ∀ v∈List.ofFn (physicalLoad j i),
      (u.index : Word (wordBits h d copies)).val≠v.dst ∧ u.addr m≠v.dst := by
    intro _ hu _ hv
    obtain ⟨p,rfl⟩ := List.mem_ofFn.mp hu
    obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hv
    rw [loc]
    refine ⟨?_,?_⟩
    · change (argumentAddr j i (dirInput p) : Word (wordBits h d copies)).val≠scratch h d j ⟨q.val,by omega⟩
      rw [Fin.val_cast_of_lt ((argument_low j i _ 0).trans (scratch_fits j 0))]
      exact (argument_low j i _ _).ne
    · exact ((scratch_separate h d j.val ⟨q.val,by omega⟩ ⟨p.val,by omega⟩).trans_le (Nat.le_add_right _ _)).ne'
  have nodup : ((List.ofFn (physicalLoad j i)).map Record.Load.dst).Nodup := by
    rw [List.map_ofFn,List.nodup_ofFn]
    intro x y eqn
    change scratch h d j ⟨x.val,by omega⟩=scratch h d j ⟨y.val,by omega⟩ at eqn
    unfold scratch at eqn
    exact Fin.ext (Nat.add_left_cancel eqn)
  have got := Record.prepared_lookup (recordAdvice h d j.val) (recordRow h d j.val i.val) (recordScratch h d j.val) m
    (by rw [physical_dirs];exact apart) (by rw [physical_dirs];exact nodup) (physicalLoad j i k)
    (by rw [physical_dirs];exact List.mem_ofFn.mpr ⟨k,rfl⟩)
  change preparedMemory j i m _=m _ at got
  rw [loc] at got
  apply got.trans
  obtain ⟨l,_,lm,_⟩ := directory_bases hd j m rom left
  obtain ⟨_,r',_,rm⟩ := directory_bases hd j m rom right
  obtain ⟨wo,so⟩ := row_offsets hd j m rom r
  fin_cases k
  · exact l
  · exact r'
  · exact lm
  · exact rm
  · exact wo
  · exact so

end
end Hierarchy.ProbeStage.Native

end OAI

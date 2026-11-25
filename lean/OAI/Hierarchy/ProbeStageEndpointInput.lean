import OAI.Hierarchy.ProbeStagePhysicalDirectory
import OAI.Hierarchy.ProbeStageRecordOutputs
import OAI.Hierarchy.ProbeStagePhysicalChoice

namespace OAI
/-! # Reading a true endpoint input from the fixed banks and true earlier counts -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section

variable {h d : ℕ} (hd : 1≤d) (j : Fin (rounds d)) (i : Fin (2^h))
local notation "W" => ramWidth h d

/-- All inputs refer to the incoming memory before any rank, count or mask changes. -/
structure SideSource (left : Bool) (b : Fin (groupBlocks h d j.val)) (c : Fin (radix h d))
    (r : ℕ) (m : Memory W) : Prop where
  rom : immutable h d W j m
  countPtr : m ((physicalSide j i left).counterBase:Word W).val=(blockCountBase h d j.val left b:Word W)
  maskPtr : m (scratch h d j.val (maskTemp left))=(blockMaskBase h d j.val left b:Word W)
  selected : m ((physicalSide j i left).chosen:Word W).val=(c.val:Word W)
  counter : (m (counterLocation h d j.val left b c)).val=r
  room : r<quota (radix h d)

include hd in
theorem setup_other (l : Bool) (b : Fin (groupBlocks h d j.val)) (c : Fin (radix h d)) (r : ℕ) (m : Memory W)
    (read : SideSource j i l b c r m) (x : Cell h d) (apart : x∉coreTargets hd j i l b c) :
    RankUpdate.prepared (physicalSide j i l) m (x.addr j.val)=m (x.addr j.val) := by
  apply RankUpdate.updates_elsewhere _ _ (rank_storage hd j i l m b c read.countPtr read.selected)
  rw [physical_touched hd j i l m b c read.countPtr read.selected]
  intro hx
  obtain ⟨y,hy,eqn⟩ := List.mem_map.mp hx
  exact apart ((cell_injective h d j.val eqn) ▸ hy)

include hd in
theorem endpoint_input (l : Bool) (b : Fin (groupBlocks h d j.val)) (c : Fin (radix h d)) (rank : ℕ) (m : Memory W)
    (src : SideSource j i l b c rank m) :
    Record.EndpointInput (physicalSide j i l) m rank (formatAdvice h d).row c (fieldWidth h)
      (packedPlace h d j.val l b) (frozenMask j l b) := by
  let s := physicalSide j i l
  have dr := rank_storage hd j i l m b c src.countPtr src.selected
  have div := countAddress hd j i l m b c src.countPtr src.selected
  have countEq : (RankUpdate.counter s m).val=counterLocation h d j.val l b c := by
    simpa [s,countTag,Cell.addr,counterLocation,Nat.add_assoc] using div
  have headNum : s.head=scratch h d j.val 10 := rfl
  have hc := c.isLt.trans_le (region_room hd j.isLt.le).2.1
  have headers := occurrence_header hd j m src.rom c
  have headRead : RankUpdate.dirWord s.heads s.chosen m=((c.val*directoryCapacity (radix h d) (stringLength h):ℕ):Word W) := by
    change m ((region h d j.val 8:Word W)+m ((physicalSide j i l).chosen:Word W).val).val=_
    rw [src.selected,add_word (region_word j.isLt 8 hc)]
    exact headers.1
  have lengthRead : RankUpdate.dirWord s.lengths s.chosen m=((PackedMask.occurrences (formatAdvice h d).row c).length:Word W) := by
    change m ((region h d j.val 9:Word W)+m ((physicalSide j i l).chosen:Word W).val).val=_
    rw [src.selected,add_word (region_word j.isLt 9 hc)]
    exact headers.2
  have lenFit : (PackedMask.occurrences (formatAdvice h d).row c).length<2^W :=
    ((occurrence_length _ c).trans (region_room hd j.isLt.le).2.2.2.1).trans_lt (regionSize_fits (h:=h) (d:=d) j)
  have rom : immutable h d W j (RankUpdate.prepared s m) := by
    intro k off small
    let x : Cell h d := .area ⟨k.val,by omega⟩ ⟨off,small⟩
    have tagNe : (⟨k.val,by omega⟩ : Fin 16) ≠ countArea l := by
      intro eqn
      have numbers := congrArg Fin.val eqn
      have low := k.isLt
      cases l <;> norm_num [countArea] at numbers <;> omega
    have far : x ≠ countTag hd j l b c := fun eqn => tagNe (Cell.area.inj eqn).1
    have other : x∉coreTargets hd j i l b c := by
      simp only [coreTargets,List.mem_cons,List.not_mem_nil,or_false]
      rintro (bad|bad|bad|eqn|bad|bad) <;> first | exact far eqn | simp [x] at bad
    exact (setup_other hd j i _ _ _ _ _ src x other).trans (src.rom k off small)
  have baseRead : RankUpdate.prepared s m (scratch h d j.val (maskTemp l))=(blockMaskBase h d j.val l b:Word W) := by
    have other : Cell.temp (maskTemp l)∉coreTargets hd j i l b c := by cases l <;> simp [maskTemp,coreTargets,countTag]
    exact (setup_other hd j i _ _ _ _ _ src _ other).trans src.maskPtr
  have hhead : RankUpdate.prepared s m (scratch h d j.val 10)=_ :=
    (RankUpdate.prepared_head s m dr).trans headRead
  have safe := quota_fits (h:=h) (d:=d) hd
  refine ⟨dr,by rw [countEq,src.counter],safe,(Nat.succ_le_of_lt src.room).trans_lt safe,?_,
    finite_directory hd j i l b c rank m rom hhead baseRead,?_,?_⟩
  · rw [lengthRead,Fin.val_cast_of_lt lenFit]
  · cases l <;> apply rank_frozen hd j
  · rw [div]
    exact area_frozen hd j l b (countArea l) _ (count_offset hd j.isLt.le b c) (mask_counter_disjoint l l).symm

end
end Hierarchy.ProbeStage.Native

end OAI

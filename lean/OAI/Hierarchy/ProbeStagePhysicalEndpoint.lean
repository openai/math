import OAI.Hierarchy.ProbeStagePhysicalEdits
import OAI.Hierarchy.ProbeStageCellAddress
import OAI.Hierarchy.ProbeStageProgram

namespace OAI
/-! # Separated rank, counter and scratch words of the installed endpoint routine -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section

variable {h d : ℕ} (hd : 1≤d) (j : Fin (rounds d))

def physicalSide (i : Fin (2^h)) (left : Bool) :=
  Record.side (recordAdvice h d j.val) (recordRow h d j.val i.val) (recordScratch h d j.val) left

def blockCountBase (h d j : ℕ) (left : Bool) (b : Fin (groupBlocks h d j)) := region h d j (countArea left)+b.val*radix h d

def countTag (left : Bool) (b : Fin (groupBlocks h d j.val)) (c : Fin (radix h d)) : Cell h d :=
  .area (countArea left) ⟨b.val*radix h d+c.val,count_offset hd j.isLt.le b c⟩

def roleRank (left : Bool) : Fin 3 := if left then 1 else 2

def countTemp (left : Bool) : Fin 12 := if left then 0 else 1

def maskTemp (left : Bool) : Fin 12 := if left then 2 else 3

def coreTargets (i : Fin (2^h)) (left : Bool) (b : Fin (groupBlocks h d j.val)) (c : Fin (radix h d)) : List (Cell h d) :=
  [.temp 8,.rank (roleRank left) i,.temp 9,countTag hd j left b c,.temp 10,.temp 11]

def coreReads (i : Fin (2^h)) (left : Bool) (c : Fin (radix h d)) : List (Cell h d) :=
  let off : Fin (regionSize h d) := ⟨c.val,c.isLt.trans_le (region_room hd j.isLt.le).2.1⟩
  [.temp (countTemp left),.rank 0 i,.area 8 off,.area 9 off]

include hd in
theorem temp_room (q : Fin 12) : scratch h d j.val q+1<2^ramWidth h d := by
  have small : 0<regionSize h d := (radix_pos h d).trans_le (region_room hd j.isLt.le).2.1
  have r0 := region_word j.isLt (0:Fin 16) small
  have before := scratch_separate h d j.val q 0
  exact (Nat.succ_le_of_lt before).trans_lt (by simpa using r0)

include hd in
theorem rank_room (k : Fin 3) (i : Fin (2^h)) : rankAddr h d j.val k i+1<2^ramWidth h d := by
  have before := rank_scratch h d j.val k i 0
  exact (Nat.succ_le_of_lt before).trans_lt (Nat.lt_of_succ_lt (temp_room (h:=h) hd j 0))

theorem countAddress (i : Fin (2^h)) (left : Bool) (m : Memory (ramWidth h d))
    (b : Fin (groupBlocks h d j.val)) (c : Fin (radix h d))
    (base : m ((physicalSide j i left).counterBase:Word (ramWidth h d)).val=(blockCountBase h d j.val left b:Word (ramWidth h d)))
    (chosen : m ((physicalSide j i left).chosen:Word (ramWidth h d)).val=(c.val:Word (ramWidth h d))) :
    (RankUpdate.counter (physicalSide j i left) m).val=Cell.addr j.val (countTag hd j left b c) := by
  rw [RankUpdate.counter,base,chosen,←Nat.cast_add,Fin.val_cast_of_lt]
  · simp [blockCountBase,countTag,Cell.addr,Nat.add_assoc]
  · simpa [blockCountBase,Nat.add_assoc] using region_word j.isLt (countArea left) (count_offset hd j.isLt.le b c)

theorem physical_touched (i : Fin (2^h)) (left : Bool) (m : Memory (ramWidth h d))
    (b : Fin (groupBlocks h d j.val)) (c : Fin (radix h d))
    (base : m ((physicalSide j i left).counterBase:Word (ramWidth h d)).val=(blockCountBase h d j.val left b:Word (ramWidth h d)))
    (chosen : m ((physicalSide j i left).chosen:Word (ramWidth h d)).val=(c.val:Word (ramWidth h d))) :
    RankUpdate.touched (physicalSide j i left) m=(coreTargets hd j i left b c).map (Cell.addr j.val) := by
  rw [RankUpdate.touched,countAddress hd j i left m b c base chosen]
  cases left <;> rfl

include hd in
theorem rank_storage (i : Fin (2^h)) (left : Bool) (m : Memory (ramWidth h d))
    (b : Fin (groupBlocks h d j.val)) (c : Fin (radix h d))
    (base : m ((physicalSide j i left).counterBase:Word (ramWidth h d)).val=(blockCountBase h d j.val left b:Word (ramWidth h d)))
    (chosen : m ((physicalSide j i left).chosen:Word (ramWidth h d)).val=(c.val:Word (ramWidth h d))) :
    RankUpdate.Distinct (physicalSide j i left) m := by
  let side := physicalSide j i left
  have ca := c.isLt.trans_le (region_room hd j.isLt.le).2.1
  have chosenNum : side.chosen=rankAddr h d j.val 0 i := rfl
  have ptrNum : side.counterBase=scratch h d j.val (countTemp left) := by cases left <;> rfl
  have targets := physical_touched hd j i left m b c base chosen
  have reads : RankUpdate.needed side m=(coreReads hd j i left c).map (Cell.addr j.val) := by
    rw [RankUpdate.needed,chosen,ptrNum,chosenNum,
      Fin.val_cast_of_lt (by have := temp_room (h:=h) hd j (countTemp left);omega : scratch h d j.val (countTemp left)<2^ramWidth h d),
      Fin.val_cast_of_lt (by have := rank_room hd j 0 i;omega : rankAddr h d j.val 0 i<2^ramWidth h d)]
    change [_,_,((region h d j.val 8:Word (ramWidth h d))+(c.val:Word (ramWidth h d))).val,((region h d j.val 9:Word (ramWidth h d))+(c.val:Word (ramWidth h d))).val]=_
    rw [add_word (region_word j.isLt 8 ca),add_word (region_word j.isLt 9 ca)]
    rfl
  refine ⟨?_,?_,?_⟩
  · rw [targets]
    apply List.Nodup.map (cell_injective h d j.val)
    cases left <;> simp [coreTargets,countTag,roleRank]
  · rw [reads,targets]
    intro x hx y hy equal
    obtain ⟨xs,hm,rfl⟩ := List.mem_map.mp hx
    obtain ⟨ys,hn,rfl⟩ := List.mem_map.mp hy
    have eqn := cell_injective h d j.val equal
    subst ys
    cases left <;> simp [coreReads,coreTargets,countTag,roleRank,countTemp,countArea] at hm hn <;> grind
  · refine ⟨temp_room (h:=h) hd j 8,?_,temp_room (h:=h) hd j 9,temp_room (h:=h) hd j 10,temp_room (h:=h) hd j 11⟩
    cases left <;> apply rank_room hd j

end
end Hierarchy.ProbeStage.Native

end OAI

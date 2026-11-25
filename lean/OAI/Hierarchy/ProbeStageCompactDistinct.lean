import OAI.Hierarchy.ProbeStageCompactWindow
import OAI.Hierarchy.ProbeStagePhysicalEndpoint

namespace OAI
/-! # Distinct read and write locations of a staged endpoint update -/
noncomputable section
namespace Hierarchy.ProbeStage.Native.Compact
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing

variable {h d : ℕ} (j : Fin (rounds d)) (i : Fin (2^h))

private def rankAt : Cell h d → Option (Fin 3)
  | .rank k r => if r=i then some k else none
  | .temp _ | .area _ _ => none

private theorem rankAt_some {x : Cell h d} {k : Fin 3} (atRow : rankAt i x=some k) :
    x=.rank k i := by
  cases x with
  | rank t r =>
    by_cases same : r=i
    · subst r
      have eqn : t=k := by simpa [rankAt] using atRow
      rw [eqn]
    · simp [rankAt,same] at atRow
  | temp _ => simp [rankAt] at atRow
  | area _ _ => simp [rankAt] at atRow

def stagedAddr (x : Cell h d) : ℕ :=
  match rankAt i x with
  | some k => base h+3+k.val
  | none => x.addr j

private theorem staged_injective (hh : 4≤h) : Function.Injective (stagedAddr j i) := by
  intro x y same
  have early:=window_before (d:=d) hh j.val
  have xx:=cell_low j x
  have yy:=cell_low j y
  unfold stagedAddr at same
  cases hx : rankAt i x with
  | none =>
    rw [hx] at same
    cases hy : rankAt i y with
    | none => rw [hy] at same; exact cell_injective h d j.val same
    | some b =>
      rw [hy] at same
      change x.addr j=base h+3+b.val at same
      omega
  | some a =>
    rw [hx] at same
    cases hy : rankAt i y with
    | none =>
      rw [hy] at same
      change base h+3+a.val=y.addr j at same
      omega
    | some b =>
      rw [hy] at same
      change base h+3+a.val=base h+3+b.val at same
      have eqn : a=b := Fin.ext (Nat.add_left_cancel same)
      rw [rankAt_some i hx,rankAt_some i hy,eqn]

def stagedSide (left : Bool) :=
  Record.side (recordAdvice h d j.val) (row h) (recordScratch h d j.val) left

local notation "W" => ramWidth h d
theorem staged_distinct (hd : 1≤d) (hh : 4≤h) (j : Fin (rounds d)) (i : Fin (2^h)) (left : Bool)
    (b : Fin (groupBlocks h d j.val)) (c : Fin (radix h d)) (m : Memory W)
    (ptr : m ((stagedSide (h:=h) j left).counterBase : Word W).val=(blockCountBase h d j.val left b : Word W))
    (chosen : m ((stagedSide (h:=h) j left).chosen : Word W).val=(c.val : Word W)) :
    RankUpdate.Distinct (stagedSide (h:=h) j left) m := by
  let side:=stagedSide (h:=h) j left
  have cfit:=c.isLt.trans_le (region_room hd j.isLt.le).2.1
  have start:=window_before (d:=d) hh j.val
  have low:=cell_low (h:=h) j (.temp 0)
  have top:=temp_room (h:=h) hd j 0
  change phase h d copies j≤ scratch h d j 0 at low
  have room : base h+8<2^W := by omega
  have ca : (RankUpdate.counter side m).val=Cell.addr j.val (countTag hd j left b c) := by
    rw [RankUpdate.counter,ptr,chosen,←Nat.cast_add,Fin.val_cast_of_lt]
    · simp [blockCountBase,countTag,Cell.addr,Nat.add_assoc]
    · simpa [blockCountBase,Nat.add_assoc] using region_word j.isLt (countArea left) (count_offset hd j.isLt.le b c)
  have targets : RankUpdate.touched side m=(coreTargets hd j i left b c).map (stagedAddr j i) := by
    rw [RankUpdate.touched,ca]
    cases left <;> simp only [coreTargets,List.map_cons,List.map_nil,stagedAddr,rankAt,countTag] <;> rfl
  have ptrNum : side.counterBase=scratch h d j.val (countTemp left) := by cases left <;> rfl
  have chosenNum : side.chosen=base h+3 := rfl
  have reads : RankUpdate.needed side m=(coreReads hd j i left c).map (stagedAddr j i) := by
    rw [RankUpdate.needed,chosen,ptrNum,chosenNum,
      Fin.val_cast_of_lt (by have := temp_room (h:=h) hd j (countTemp left);omega : scratch h d j.val (countTemp left)<2^W),
      Fin.val_cast_of_lt (by omega : base h+3<2^W)]
    change [_,_,((region h d j.val 8:Word W)+(c.val:Word W)).val,((region h d j.val 9:Word W)+(c.val:Word W)).val]=_
    rw [add_word (region_word j.isLt 8 cfit),add_word (region_word j.isLt 9 cfit)]
    simp only [coreReads,List.map_cons,List.map_nil,stagedAddr,rankAt]; rfl
  have embed:=staged_injective j i hh
  refine ⟨?_,?_,?_⟩
  · rw [targets]
    apply List.Nodup.map embed
    cases left <;> simp [coreTargets,countTag,roleRank]
  · rw [reads,targets]
    intro x hx y hy equal
    obtain ⟨xs,hm,rfl⟩:=List.mem_map.mp hx
    obtain ⟨ys,hn,rfl⟩:=List.mem_map.mp hy
    have eqn:=embed equal
    subst ys
    cases left <;> simp [coreReads,coreTargets,countTag,roleRank,countTemp,countArea] at hm hn <;> grind
  · refine ⟨temp_room (h:=h) hd j 8,?_,temp_room (h:=h) hd j 9,temp_room (h:=h) hd j 10,temp_room (h:=h) hd j 11⟩
    cases left
    · change base h+5+1<2^W; omega
    · change base h+4+1<2^W; omega

end Hierarchy.ProbeStage.Native.Compact
end

end OAI

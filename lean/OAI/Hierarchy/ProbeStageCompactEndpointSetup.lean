import OAI.Hierarchy.ProbeStageCompactDistinct
import OAI.Hierarchy.ProbeStagePhysicalOrdinal

namespace OAI
/-! # The literal six writes that prepare a saturation scatter -/

namespace Hierarchy.ProbeStage.Native.Compact
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section

variable {h d : ℕ} (j : Fin (rounds d)) (i : Fin (2^h))
local notation "W" => ramWidth h d
local notation "A" => recordAdvice h d j
local notation "S" => recordScratch h d j

/-- The mutable count, the two immutable directory reads and the captured rank
are computed from the same physical words before either endpoint is changed. -/
theorem endpoint_prepared (hd : 1≤ d) (hh : 4≤ h) (l : Bool) (b : Fin (groupBlocks h d j.val))
    (c : Fin (radix h d)) (r : ℕ) (m n : Memory W) (saved : Fin 8→ Word W)
    (rel : Model j i saved m n) (s : SideSource j i l b c r m) :
    Model j i saved (RankUpdate.prepared (physicalSide j i l) m)
      (RankUpdate.prepared (Record.side A (row h) S l) n) := by
  let f:=physicalSide j i l
  let g:=Record.side A (row h) S l
  have hide:=window_before (d:=d) hh j
  have above:=cell_low (h:=h) j (.temp 0)
  change _≤ scratch h d j 0 at above
  have room : scratch h d j 0<2^W := scratch_fits j 0
  have selectRoom : base h+3<2^W := by omega
  have origRoom : rankAddr h d j 0 i<2^W := by have := rank_room hd j 0 i;omega
  have picked : n (g.chosen:Word W).val=m (f.chosen:Word W).val := by
    change n ((base h+3:ℕ):Word W).val=m ((rankAddr h d j 0 i):Word W).val
    rw [Fin.val_cast_of_lt selectRoom,Fin.val_cast_of_lt origRoom]
    simpa only [Fin.val_zero,Nat.add_zero] using rel.result 0
  have cp : g.counterBase=scratch h d j (countTemp l) := by cases l <;> rfl
  have oldcp : f.counterBase=scratch h d j (countTemp l) := by cases l <;> rfl
  have counted : n (g.counterBase:Word W).val=m (f.counterBase:Word W).val := by
    rw [cp,oldcp,Fin.val_cast_of_lt (scratch_fits j _)]
    exact rel.common _ (common_temp j i hh _)
  have ptr : RankUpdate.counter g n=RankUpdate.counter f m := congrArg₂ (fun x y : Word W=>x+y) counted picked
  have countLoc : Common j i (RankUpdate.counter f m).val := by
    have atCounter:=countAddress hd j i l m b c s.countPtr s.selected
    have low:=common_area j i hh (countArea l) ⟨b.val*radix h d+c.val,count_offset hd j.isLt.le b c⟩
    rw [atCounter]
    exact low
  have previous : n (RankUpdate.counter g n).val=m (RankUpdate.counter f m).val := by
    rw [ptr];exact rel.common _ countLoc
  have inc : RankUpdate.newCount g n=RankUpdate.newCount f m := congrArg (·+1) previous
  have bound:=c.isLt.trans_le (region_room hd j.isLt.le).2.1
  have dir (k : Fin 16) : RankUpdate.dirWord (region h d j k) g.chosen n =
      RankUpdate.dirWord (region h d j k) f.chosen m := by
    unfold RankUpdate.dirWord
    rw [picked,s.selected,add_word (region_word j.isLt k bound)]
    exact rel.common _ (common_area j i hh k ⟨c.val,bound⟩)
  have head : RankUpdate.dirWord g.heads g.chosen n=RankUpdate.dirWord f.heads f.chosen m := dir 8
  have len : RankUpdate.dirWord g.lengths g.chosen n=RankUpdate.dirWord f.lengths f.chosen m := dir 9
  have a:=rel.update_common (common_temp j i hh 8) (RankUpdate.counter f m)
  have z:=a.update_result (roleRank l) (m (RankUpdate.counter f m).val)
  have rankF : f.rank=rankAddr h d j (roleRank l) i := by cases l <;> rfl
  have rankG : g.rank=base h+3+(roleRank l).val := by cases l <;> rfl
  have y:=z.update_common (common_temp j i hh 9) (RankUpdate.newCount f m)
  have t:=y.update_common countLoc (RankUpdate.newCount f m)
  have e:=t.update_common (common_temp j i hh 10) (RankUpdate.dirWord f.heads f.chosen m)
  have fin:=e.update_common (common_temp j i hh 11)
    (if RankUpdate.newCount f m=(f.quota:Word W) then RankUpdate.dirWord f.lengths f.chosen m else 0)
  have fSep:=rank_storage hd j i l m b c s.countPtr s.selected
  have gSep:=staged_distinct hd hh j i l b c n (counted.trans s.countPtr) (picked.trans s.selected)
  change Model j i saved (RankUpdate.prepared f m) (RankUpdate.prepared g n)
  rw [RankUpdate.prepared_eq f m fSep,RankUpdate.prepared_eq g n gSep]
  unfold RankUpdate.updates
  rw [inc,head,len,previous,ptr,rankF,rankG]
  exact fin

end
end Hierarchy.ProbeStage.Native.Compact

end OAI

import OAI.Hierarchy.ProbeStagePhysicalStart

namespace OAI
/-! # Passing the real destination bank through the preceding source commit -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section

variable {h d : ℕ} (hd : 1≤d) (j : Fin (rounds d)) (i : Fin (2^h))
local notation "W" => ramWidth h d

theorem countTag_addr (l : Bool) (b : Fin (groupBlocks h d j.val)) (c : Fin (radix h d)) :
    Cell.addr j.val (countTag hd j l b c)=counterLocation h d j.val l b c := by simp [countTag,Cell.addr,counterLocation,Nat.add_assoc]

variable {l : Bool} {b : Fin (groupBlocks h d j.val)} {c : Fin (radix h d)} {r : ℕ} {m : Memory (ramWidth h d)}

theorem commit_rom (out : Commit (h:=h) (d:=d) hd j i l b c r m) (rom : immutable h d W j m) :
    immutable h d W j (RankUpdate.image (physicalSide j i l) m) := by
  intro k o small
  let x : Cell h d := .area ⟨k.val,by omega⟩ ⟨o,small⟩
  refine (commit_typed_frame hd j i out x ?_ ?_).trans (rom k o small)
  · have far : x ≠ countTag hd j l b c := by
      intro eqn
      have numbers := congrArg Fin.val (Cell.area.inj eqn).1
      have low := k.isLt
      cases l <;> norm_num [countArea] at numbers <;> omega
    simp only [coreTargets,List.mem_cons,List.not_mem_nil,or_false]
    rintro (bad|bad|bad|eqn|bad|bad) <;> first | exact far eqn | simp [x] at bad
  · intro row chunk eqn
    have numbers := congrArg Fin.val (Cell.area.inj eqn).1
    have low := k.isLt
    cases l <;> norm_num [maskArea] at numbers <;> omega

theorem commit_ptr (out : Commit (h:=h) (d:=d) hd j i l b c r m) (k : Fin 12) (low : k.val<8) :
    RankUpdate.image (physicalSide j i l) m (scratch h d j.val k)=m (scratch h d j.val k) := by
  apply commit_typed_frame hd j i out (.temp k)
  · simp [coreTargets,countTag];omega
  · intro row chunk; simp [maskTag]

theorem commit_rank_frame (out : Commit (h:=h) (d:=d) hd j i l b c r m) (k : Fin 3) (other : k≠roleRank l) :
    RankUpdate.image (physicalSide j i l) m (rankAddr h d j.val k i)=m (rankAddr h d j.val k i) := by
  apply commit_typed_frame hd j i out (.rank k i)
  · simp [coreTargets,countTag,other]
  · intro row chunk; simp [maskTag]

theorem commit_other_counter (out : Commit (h:=h) (d:=d) hd j i l b c r m) (l' : Bool) (ne : l'≠l)
    (b' : Fin (groupBlocks h d j.val)) (c' : Fin (radix h d)) :
    RankUpdate.image (physicalSide j i l) m (counterLocation h d j.val l' b' c')=m (counterLocation h d j.val l' b' c') := by
  rw [←countTag_addr hd]
  apply commit_typed_frame hd j i out
  · cases l <;> cases l' <;> simp_all [coreTargets,countTag,countArea]
  · intro row chunk;cases l <;> cases l' <;> simp [maskTag,countTag,maskArea,countArea]

theorem commit_other_mask (out : Commit (h:=h) (d:=d) hd j i l b c r m) (l' : Bool) (ne : l'≠l)
    (b' : Fin (groupBlocks h d j.val)) (row : MaskIndex (radix h d)) (chunk : Fin (fieldChunks h)) :
    RankUpdate.image (physicalSide j i l) m (maskLocation h d j.val l' b' row chunk)=m (maskLocation h d j.val l' b' row chunk) := by
  rw [←maskTag_addr hd]
  apply commit_typed_frame hd j i out
  · cases l <;> cases l' <;> simp [coreTargets,maskTag,countTag,maskArea,countArea]
  · intro u k;cases l <;> cases l' <;> simp_all [maskTag,maskArea]

theorem after_left {rb : Fin (groupBlocks h d j.val)} {rr : ℕ} (out : Commit (h:=h) (d:=d) hd j i true b c r m)
    (src : SideSource j i false rb c rr m) : SideSource j i false rb c rr (RankUpdate.image (physicalSide j i true) m) := by
  constructor
  · exact commit_rom hd j i out src.rom
  · have addr : ((physicalSide j i false).counterBase:Word W).val=scratch h d j.val 1 := Fin.val_cast_of_lt (scratch_fits (h:=h) j 1)
    rw [addr]
    exact (commit_ptr hd j i out 1 (by decide)).trans (by rw [←addr];exact src.countPtr)
  · exact (commit_ptr hd j i out 3 (by decide)).trans src.maskPtr
  · have addr : ((physicalSide j i false).chosen:Word W).val=rankAddr h d j.val 0 i :=
      Fin.val_cast_of_lt (Nat.lt_of_succ_lt (rank_room hd j 0 i))
    rw [addr]
    exact (commit_rank_frame hd j i out 0 (by decide)).trans (by rw [←addr];exact src.selected)
  · rw [commit_other_counter hd j i out false (by decide),src.counter]
  · exact src.room

end
end Hierarchy.ProbeStage.Native

end OAI

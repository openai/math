import OAI.Hierarchy.ProbeStageOpposite
import OAI.Hierarchy.ProbeStageDistinctBlocks

namespace OAI
/-! # One ordinal advances every actual mutable array in both endpoints -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section
attribute [local instance] Classical.decEq

variable {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d)) (i : Fin (2^h))
local notation "W" => ramWidth h d
local notation "A" => recordAdvice h d j.val
local notation "S" => recordScratch h d j.val
local notation "recRow" => recordRow h d j.val i.val

abbrev OrdCommit {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d)) (i : Fin (2^h))
    (l : Bool) (m : Memory (ramWidth h d)) := Commit (h:=h) (d:=d) hd j i l (ordinalBlock hd j i π l) ((assigned j π).color i) (sideRank π j l i).val m

theorem update_counter {l : Bool} {m : Memory (ramWidth h d)} (out : OrdCommit (h:=h) (d:=d) hd π j i l m)
    (source : SideSource j i l (ordinalBlock hd j i π l) ((assigned j π).color i) (sideRank π j l i).val m) (b : _) (c : Fin (radix h d)) :
    let t := counterLocation h d j.val l (blockNumber hd j π b) c
    RankUpdate.image (physicalSide j i l) m t=if endpointKey j π l i=b ∧ ((assigned j π).color i)=c then m t+1 else m t := by
  classical
  dsimp only
  by_cases hit : endpointKey j π l i=b ∧ ((assigned j π).color i)=c
  · obtain ⟨rfl,rfl⟩ := hit
    rw [ite_eq_left ⟨rfl,rfl⟩]
    have fit := source.room.trans (quota_fits hd)
    have saved : m (counterLocation h d j.val l (ordinalBlock hd j i π l) ((assigned j π).color i))=((sideRank π j l i).val:Word W) :=
      Fin.ext (by rw [Fin.val_cast_of_lt fit];exact source.counter)
    let addr := counterLocation h d j.val l (ordinalBlock hd j i π l) ((assigned j π).color i)
    change RankUpdate.image (physicalSide j i l) m addr=m addr+1
    change m addr=_ at saved
    calc
      _ = (((sideRank π j l i).val+1 : ℕ):Word W) :=
        Fin.ext (out.counter.trans (Fin.val_cast_of_lt ((Nat.succ_le_of_lt source.room).trans_lt (quota_fits hd))).symm)
      _ = _ := by rw [saved,Nat.cast_add,Nat.cast_one]
  · rw [ite_eq_right hit,←countTag_addr hd]
    apply commit_typed_frame hd j i out
    · simp only [coreTargets,List.mem_cons,List.not_mem_nil,or_false]
      intro member
      rcases member with bad|bad|bad|eqn|bad|bad <;> try cases bad
      have nums := (countTag_eq_iff hd j l).mp eqn
      exact hit ⟨((blockNumber_injective hd j π) nums.1).symm,nums.2.symm⟩
    · intro row k; cases l <;> simp [countTag,maskTag,countArea,maskArea]

theorem update_mask {l : Bool} {m : Memory (ramWidth h d)} (out : OrdCommit (h:=h) (d:=d) hd π j i l m) (b : _) (r : MaskIndex (radix h d))
    (k : Fin (fieldChunks h)) (initial :
      m (maskLocation h d j.val l (blockNumber hd j π b) r k)=
        (PackedMask.word ((formatAdvice h d).row r) (Greedy.prefixFull (endpointKey j π l) (assigned j π).color i.val b)
          (fieldWidth h) k.val:Word W)) :
    let addr := maskLocation h d j.val l (blockNumber hd j π b) r k
    let full := Greedy.prefixFull (endpointKey j π l) (assigned j π).color i.val b
    RankUpdate.image (physicalSide j i l) m addr=if endpointKey j π l i=b ∧ (sideRank π j l i).val+1=quota (radix h d)
      then (PackedMask.word ((formatAdvice h d).row r) (insert ((assigned j π).color i) full) (fieldWidth h) k.val:Word W) else m addr := by
  classical
  dsimp only
  have bound (f : Finset (Fin (radix h d))) := (PackedMask.word_lt ((formatAdvice h d).row r) f (fieldWidth h) k.val).trans_le
    ((least_size h d).trans (regionSize_fits (h:=h) (d:=d) j).le)
  by_cases block : endpointKey j π l i=b
  · subst b
    let full := Greedy.prefixFull (endpointKey j π l) (assigned j π).color i.val (endpointKey j π l i)
    have start : (m (maskLocation h d j.val l (ordinalBlock hd j i π l) r k)).val=
        PackedMask.word ((formatAdvice h d).row r) full (fieldWidth h) k.val :=
      (congrArg Fin.val initial).trans (Fin.val_cast_of_lt (bound full))
    have actual := out.masks r k full start
    apply Fin.ext
    by_cases sat : (sideRank π j l i).val+1=quota (radix h d)
    · simpa only [full,ordinalBlock,queryBlock,eq_self_iff_true,true_and,ite_eq_left sat,Fin.val_cast_of_lt (bound _)] using actual
    · simpa only [full,ordinalBlock,queryBlock,eq_self_iff_true,true_and,ite_eq_right sat,initial,
        Fin.val_cast_of_lt (bound _)] using actual
  · have no : ¬(endpointKey j π l i=b ∧ (sideRank π j l i).val+1=quota (radix h d)) :=
      fun hit=>block hit.1
    rw [ite_eq_right no,←maskTag_addr hd]
    apply commit_typed_frame hd j i out
    · cases l <;> simp [coreTargets,maskTag,countTag,maskArea,countArea]
    · intro s t
      exact maskTag_ne_of_block_ne hd j l (fun eqn=>block ((blockNumber_injective hd j π eqn).symm)) r s k t

theorem both_advance {m : Memory (ramWidth h d)} (pre : PrefixState hd π j i.val m)
    (ls : SideSource j i true (ordinalBlock hd j i π true) ((assigned j π).color i) (sideRank π j true i).val (atCommits j i m))
    (rs : SideSource j i false (ordinalBlock hd j i π false) ((assigned j π).color i) (sideRank π j false i).val (Record.rightInput A S recRow m))
    (left : OrdCommit (h:=h) (d:=d) hd π j i true (atCommits j i m)) (right : OrdCommit (h:=h) (d:=d) hd π j i false (Record.rightInput A S recRow m)) :
    PrefixState hd π j (i.val+1) (Record.image A S recRow m) := by
  apply prefix_advance π j hd i m _ pre
  · intro l b c;dsimp only
    cases l
    · rw [show Record.image A S recRow m _=_ from update_counter hd π j i right rs b c]
      rw [show Record.rightInput A S recRow m _=_ from commit_other_counter (l:=true) hd j i left false (by decide) _ _,commit_counter_start]
    · rw [show Record.image A S recRow m _=_ from commit_other_counter (l:=false) hd j i right true (by decide) _ _,
        show Record.rightInput A S recRow m _=_ from update_counter hd π j i left ls b c,commit_counter_start]
  · intro l b r k;dsimp only
    cases l
    · have first := (commit_other_mask (l:=true) hd j i left false (by decide) (blockNumber hd j π b) r k).trans (commit_mask_start j i m _ _ _ _)
      rw [show Record.image A S recRow m _=_ from update_mask hd π j i right b r k (first.trans (pre.2 false b r k)),
        show Record.rightInput A S recRow m _=_ from first]
    · rw [show Record.image A S recRow m _=_ from commit_other_mask (l:=false) hd j i right true (by decide) _ _ _,
        show Record.rightInput A S recRow m _=_ from update_mask hd π j i left b r k ((commit_mask_start j i m _ _ _ _).trans (pre.2 true b r k)),commit_mask_start]

end
end Hierarchy.ProbeStage.Native

end OAI

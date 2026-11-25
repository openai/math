import OAI.Hierarchy.ProbeStagePhysicalCommit
import OAI.Hierarchy.ProbeStagePrefixAdvance
import OAI.Hierarchy.ProbeStageRecordFrame

namespace OAI
/-! # Both endpoints read the chosen word and the actual earlier prefix before commits -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section

variable {h d : ℕ} (hd : 1≤d) (j : Fin (rounds d)) (i : Fin (2^h))
local notation "W" => ramWidth h d
local notation "A" => recordAdvice h d j.val
local notation "S" => recordScratch h d j.val
local notation "R" => recordRow h d j.val i.val

def ordinalBlock (π : Equiv.Perm (Fin (2^h))) (left : Bool) := blockNumber hd j π (queryBlock j i π left)
def atCommits (m : Memory W) := Record.leftInput A S R m

theorem scratch_atCommits (m : Memory W) (k : Fin 6) :
    atCommits j i m (scratch h d j.val ⟨k.val,by omega⟩)=preparedMemory j i m (scratch h d j.val ⟨k.val,by omega⟩) := by
  apply Record.left_prepared
  · apply scratch_ne j
    intro eqn
    have nums := congrArg Fin.val eqn
    change k.val=6 at nums
    omega
  · exact (chosen_low j i _).ne'
  · apply scratch_ne j
    intro eqn
    have nums := congrArg Fin.val eqn
    change k.val=7 at nums
    omega
  · exact scratch_fits (h:=h) j 7

theorem commits_region (m : Memory W) (k : Fin 16) (off : ℕ) :
    atCommits j i m (region h d j.val k+off)=m (region h d j.val k+off) := by
  have above (r : Fin 12) : scratch h d j.val r<region h d j.val k+off :=
    (scratch_separate h d j.val r k).trans_le (Nat.le_add_right _ _)
  rw [atCommits,Record.left_prepared _ _ _ _ _ (above 6).ne' ((chosen_low j i 7).trans (above 7)).ne'
    (above 7).ne' (scratch_fits (h:=h) j 7)]
  apply prepared_region

theorem commit_counter_start (m : Memory W) (l : Bool) (b : Fin (groupBlocks h d j.val)) (c : Fin (radix h d)) :
    atCommits j i m (counterLocation h d j.val l b c)=m (counterLocation h d j.val l b c) := by
  simpa [counterLocation,Nat.add_assoc] using commits_region j i m (countArea l) (b.val*radix h d+c.val)

theorem commit_mask_start (m : Memory W) (l : Bool) (b : Fin (groupBlocks h d j.val)) (r : MaskIndex (radix h d))
    (k : Fin (fieldChunks h)) : atCommits j i m (maskLocation h d j.val l b r k)=m (maskLocation h d j.val l b r k) := by
  simpa [maskLocation,Nat.add_assoc] using commits_region j i m (maskArea l)
    (b.val*((radix h d)^4*fieldChunks h)+(rowCode r*fieldChunks h+k.val))

include hd in
theorem start_side (π : Equiv.Perm (Fin (2^h))) (m : Memory W) (rom : immutable h d W j m)
    (stored : ∀ q,m (argumentAddr j i q)=(Endpoints.words (history h d π j.val).tiles (radix_pos h d)
      (history h d π j.val).encode i q:Word W)) (before : PrefixState hd π j i.val m) (l : Bool) :
    SideSource j i l (ordinalBlock hd j i π l) ((assigned j π).color i) (sideRank π j l i).val (atCommits j i m) := by
  let b := ordinalBlock hd j i π
  have ready := prepared_word j i hd m rom (b true) (b false) (queryRow j i π) (ordinalIDs_of_words j i hd π m stored)
  have choice := (ordinal_choice hd j i π m rom stored before).2
  have rankSmall := (sideRank π j l i).isLt.trans (quota_fits (h:=h) (d:=d) hd)
  constructor
  · intro k off small
    exact (commits_region j i m _ _).trans (rom k off small)
  · have addr : (physicalSide j i l).counterBase=scratch h d j.val (countTemp l) := by cases l <;> rfl
    rw [addr,Fin.val_cast_of_lt (scratch_fits (h:=h) j _)]
    cases l
    · exact (scratch_atCommits j i m 1).trans (ready 1)
    · exact (scratch_atCommits j i m 0).trans (ready 0)
  · cases l
    · exact (scratch_atCommits j i m 3).trans (ready 3)
    · exact (scratch_atCommits j i m 2).trans (ready 2)
  · have addr : (physicalSide j i l).chosen= (recordRow h d j.val i.val).chosen := by cases l <;> rfl
    rw [addr,Fin.val_cast_of_lt ((chosen_low j i 0).trans (scratch_fits (h:=h) j 0))]
    exact choice
  · rw [commit_counter_start,ordinalBlock,queryBlock,before.1 l _ _,←rank_at π j l i,Fin.val_cast_of_lt rankSmall]
  · exact (sideRank π j l i).isLt

end
end Hierarchy.ProbeStage.Native

end OAI

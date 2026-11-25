import OAI.Hierarchy.ProbeStageOrdinalPrefix
import OAI.Hierarchy.ProbeStageOrdinalFrame
import OAI.Hierarchy.ProbeStageVisit

namespace OAI
/-! # The closed correctness theorem for the actual native allocator row -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section

/-- Execute one record from its three physical ID words, the fixed ROM and the earlier
prefix. The conclusion includes the true color/ranks, both evolving banks, and the
runtime charges measured on these same physical images. -/
theorem physical_ordinal {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d)) : RowCorrect hd π j := by
  intro i m rom ids pre
  have ls := start_side hd j i π m rom ids pre true
  have left := endpoint_commit hd j i _ _ _ _ _ ls
  have rs := after_left hd j i left (start_side hd j i π m rom ids pre false)
  have right := endpoint_commit hd j i _ _ _ _ _ rs
  have choice := ordinal_choice hd j i π m rom ids pre
  have rstep : Record.rightInput (recordAdvice h d j.val) (recordScratch h d j.val) (recordRow h d j.val i.val) m
    (rankAddr h d j.val 0 i)=atCommits j i m (rankAddr h d j.val 0 i) := commit_rank_frame hd j i left 0 (by decide)
  have o0 := commit_rank_frame hd j i right 0 (by decide)
  have o1 := commit_rank_frame hd j i right 1 (by decide)
  refine ⟨both_advance hd π j i pre ls rs left right,?_,choice.1.le,?_,?_⟩
  · intro k
    fin_cases k
    · exact o0.trans (rstep.trans choice.2)
    · apply o1.trans
      apply Fin.ext
      exact left.rank.trans (Fin.val_cast_of_lt (((assigned j π).enterRank i).isLt.trans (quota_fits (h:=h) (d:=d) hd))).symm
    · apply Fin.ext
      exact right.rank.trans (Fin.val_cast_of_lt (((assigned j π).exitRank i).isLt.trans (quota_fits (h:=h) (d:=d) hd))).symm
  · change RankUpdate.occurrenceCount (physicalSide j i true) (atCommits j i m) +
      RankUpdate.occurrenceCount (physicalSide j i false) (RankUpdate.image (physicalSide j i true) (atCommits j i m)) ≤ _
    rw [left.clears,right.clears]
    have paid (r : Fin (quota (radix h d))) :
        (RankUpdate.edits (formatAdvice h d).row ((assigned j π).color i) r.val (quota (radix h d))).length =
          saturationWrites (formatAdvice h d).row ((assigned j π).color i) r := by
      by_cases full : r.val+1=quota (radix h d) <;> simp [RankUpdate.edits,saturationWrites,full]
    exact (congrArg₂ Nat.add (paid ((assigned j π).enterRank i)) (paid ((assigned j π).exitRank i))).le
  · intro x hx
    exact (outside_frame hd j i right x hx).trans ((outside_frame hd j i left x hx).trans (start_frame j i m x hx))

end
end Hierarchy.ProbeStage.Native

end OAI

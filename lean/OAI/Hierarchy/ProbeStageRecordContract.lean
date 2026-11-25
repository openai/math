import OAI.Hierarchy.ProbeStageCellAddress
import OAI.Hierarchy.ProbeStageProgram
import OAI.Hierarchy.ProbeStageHistoryCost
import OAI.Hierarchy.ProbeStagePrefixMemory

namespace OAI
/-! # Observable effect of an ordinal on the phase's physical banks -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM
open scoped Fin.CommRing

def MayWrite (h d j : ℕ) (i : Fin (2^h)) (x : ℕ) : Prop :=
  (∃ k : Fin 3, x=rankAddr h d j k i) ∨ (∃ k : Fin 12, x=scratch h d j k) ∨
  (∃ k : Fin 4, ∃ offset : Fin (regionSize h d), x=region h d j ⟨12+k.val,by omega⟩+offset.val)

/-- A clocked row has one resulting memory: this is the image of the record code installed
in the full subdivision program. The field bounds charge this same run's private reads. -/
structure RowOutput {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d))
    (i : Fin (2^h)) (m : Memory (wordBits h d copies)) : Prop where
  next : PrefixState hd π j (i.val+1) (Record.image (recordAdvice h d j.val) (recordScratch h d j.val) (recordRow h d j.val i.val) m)
  columns : ∀ k : Fin 3, Record.image (recordAdvice h d j.val) (recordScratch h d j.val) (recordRow h d j.val i.val) m
    (rankAddr h d j.val k i)=((![(assigned j π).color i |>.val,(assigned j π).enterRank i |>.val,
      (assigned j π).exitRank i |>.val] k : ℕ) : Word _)
  scans : Record.scans (recordAdvice h d j.val) (recordScratch h d j.val) (recordRow h d j.val i.val) m ≤ expectedScans h d π j.val i
  clears : Record.clears (recordAdvice h d j.val) (recordScratch h d j.val) (recordRow h d j.val i.val) m ≤ expectedClears h d π j.val i
  frame : ∀ x, ¬ MayWrite h d j.val i x →
    Record.image (recordAdvice h d j.val) (recordScratch h d j.val) (recordRow h d j.val i.val) m x=m x

end Hierarchy.ProbeStage.Native

end OAI

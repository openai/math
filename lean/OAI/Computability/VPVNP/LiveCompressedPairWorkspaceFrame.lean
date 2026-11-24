import OAI.Computability.VPVNP.CompressorPrefixFrames
import OAI.Computability.VPVNP.LiveCompressedPairProtection

/-! # The compressed-pair tags and headers across reachable online calls -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM CompressorRecords CompressorRecords.Schedule BranchSegments
open LiveStageLink Compression

variable {w d initial phases : ℕ} {C : Catalog d} {b : Bootstrap} {plan : Online.Config C initial phases}
    {finalTable : PairTable} {pub : Fin 11 → Word w} {clock : ℕ} {s : Stage} {initialMem : Memory w}

/-- Recover the complete native prefix witnessing the reached call boundary. -/
private theorem SourceReachable.log {cursor : Word w} {mem : Memory w}
    (h : SourceReachable b plan finalTable pub clock s initialMem cursor mem) :
    ∃ bs rs, runSegment (original b plan finalTable pub s) (clockAt pub clock s) (some 0) initialMem bs = some rs ∧
      endState (some 0) rs = some cursor ∧ after initialMem (eventLog rs) = mem := by
  induction h with
  | start => exact ⟨[],[],rfl,rfl,rfl⟩
  | @more st mem bits rep st' _ call returned ih =>
    obtain ⟨bs,rs,run,state,memory⟩ := ih
    refine ⟨bs++[bits],rs++[rep],?_,?_,?_⟩
    · rw [PrimedSchedule.runSegment_append,run]
      change (runSegment _ _ (endState _ rs) (after initialMem (eventLog rs)) [bits]).map _ = _
      rw [state,memory,runSegment,call]
      rfl
    · rw [endState_append,state]
      exact returned
    · rw [SourceWalk.after_append,memory]
      simp only [eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil]

/-- Every successful online call reached by the outer component preserves
each protected word, including a call on a branch that eventually rejects. -/
theorem SourceReachable.online_keep_of_prefix {lo : ℕ}
    (stable : ∀ bs rs, runSegment (OnlineWorkspace.program plan pub) (clockAt pub clock Stage.online)
      (some 0) initialMem bs = some rs → SourceBankFrame.Stable lo initialMem rs)
    {st : Word w} {mem : Memory w} {bits : List Bool} {r : Report w}
    (reach : SourceReachable b plan finalTable pub clock Stage.online initialMem st mem)
    (call : execute (original b plan finalTable pub Stage.online) (clockAt pub clock Stage.online)
      ((original b plan finalTable pub Stage.online).start st) mem bits = some r) (x : ℕ) (hx : x < lo) :
    after mem r.events x = mem x := by
  obtain ⟨bs,rs,run,state,memory⟩ := reach.log
  have complete : runSegment (OnlineWorkspace.program plan pub) (clockAt pub clock Stage.online) (some 0)
      initialMem (bs++[bits]) = some (rs++[r]) := by
    change runSegment (original b plan finalTable pub Stage.online) _ _ _ _ = _
    rw [PrimedSchedule.runSegment_append,run]
    change (runSegment _ _ (endState _ rs) (after initialMem (eventLog rs)) [bits]).map _ = _
    rw [state,memory,runSegment,call]
    rfl
  have full := (stable _ _ complete).take_eq (rs++[r]).length x hx
  rw [List.take_length,SourceWalk.after_append,memory] at full
  have before := (stable _ _ run).take_eq rs.length x hx
  rw [List.take_length,memory] at before
  simpa only [eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil] using full.trans before.symm

variable {R : Type*} [CommSemiring R] {a g c n : ℕ} {X : Compression.State a g}
variable {E : StateExecution R c n X}
variable {trace : ExecutionTrace (OnlineWorkspace.program plan pub) (clockAt pub clock Stage.online) E (some 0) initialMem}
variable {lo : ℕ} (framed : trace.Framed lo)

include framed in
theorem SourceReachable.online_keep {st : Word w} {mem : Memory w} {bits : List Bool} {r : Report w}
    (reach : SourceReachable b plan finalTable pub clock Stage.online initialMem st mem)
    (call : execute (original b plan finalTable pub Stage.online) (clockAt pub clock Stage.online)
      ((original b plan finalTable pub Stage.online).start st) mem bits = some r) (x : ℕ) (hx : x < lo) :
    after mem r.events x = mem x :=
  reach.online_keep_of_prefix (fun _ _ run => framed.stable run) call x hx

/-- The actual recursive online trace supplies the pair linker's invariant. -/
def onlineProtected (b : Bootstrap) (finalTable : PairTable) (before : (PairTag.address pub).val < lo) :
    Protected b plan finalTable pub clock Stage.online initialMem :=
  Protected.ofSource b plan finalTable pub clock Stage.online initialMem
    (fun reach _ call _ => SourceReachable.online_keep framed reach call _ before)

/-- The same invariant protects the surrounding live tag and the virtual
header words, for every address below the descriptor pointer bank. -/
theorem onlineProtected_word (b : Bootstrap) (finalTable : PairTable)
    (before : (PairTag.address pub).val < lo) (x : ℕ) (hx : x < lo) :
    (onlineProtected framed b finalTable before).word x :=
  Protected.ofSource_word b plan finalTable pub clock Stage.online initialMem x
    (fun reach _ call _ => SourceReachable.online_keep framed reach call _ before)
    (fun reach _ call => SourceReachable.online_keep framed reach call x hx)

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI

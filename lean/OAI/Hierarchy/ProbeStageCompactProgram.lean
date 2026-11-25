import OAI.Hierarchy.ProbeStageCompactLevelCode
import OAI.Hierarchy.ProbeStageCheap
import OAI.Hierarchy.ProbeStageRegularization

namespace OAI
/-! # Instruction tape and fixed text of the counted native subdivision -/

namespace Hierarchy.ProbeStage.Native.Compact
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators
noncomputable section

open private record_text walk_text from OAI.Hierarchy.ProbeStageProgramSize
open private Supported Supported.mk Supported.code Supported.seq record_good schedule_good chronological_good from
  OAI.Hierarchy.ProbeStageCheap

private theorem body_text (h d : ℕ) (j : Fin (rounds d)) : text (body h d j)≤13256 := by
  have bound:=record_text (ramWidth h d) (recordAdvice h d j) (recordScratch h d j) (row h)
  change _≤5000+164*fieldChunks h at bound
  have cap:=(chunks_cover h).2.2
  simp only [body,text_seq,stage_text,unstage_text,stageText,unstageText]
  omega

private theorem level_text (h d : ℕ) (j : Fin (rounds d)) : text (level h d j)≤16000 := by
  let x:=endpointAt h d copies j
  let o:=operandsAt h d copies j
  let t:=tablesAt h d copies j
  have pre:=columns_text (ramWidth h d) (2^h) (allocatorBase h d copies j) 32 (List.ofFn x.term)
    (by intro e he;obtain ⟨k,rfl⟩:=List.mem_ofFn.mp he;exact x.work k)
  have post:=columns_text (ramWidth h d) (2^h) (output h d copies j) 32 (List.ofFn (field o t))
    (by intro e he;obtain ⟨k,rfl⟩:=List.mem_ofFn.mp he;exact field_work o t k)
  simp only [List.length_ofFn] at pre post
  change text (program _ (prepareRows h d j))≤_ at pre
  change text (program _ (writeRows h d j))≤_ at post
  have b:=body_text h d j
  simp only [level,dite_eq_left j.isLt,text_seq,CompactLoop.code]
  change text (program _ (prepareRows h d j)) + (63 + text (body h d j)) +
    text (program _ (writeRows h d j)) ≤ 16000
  omega

theorem subdivision_text (h d : ℕ) : text (subdivision h d)≤ codeBound d := by
  by_cases hh : 4≤ h
  · rw [subdivision,ite_eq_left hh]
    have root:=columns_text (ramWidth h d) (2^h) (2^h) 2 ([.lit 0,.row] : List Expr) (by simp [Expr.work])
    change text (program (ramWidth h d) (rootPasses h))≤53 at root
    have all_:=walk_text (program (ramWidth h d) (rootPasses h)) (level h d) (rounds d) 16000
      (fun k hk=> level_text h d ⟨k,hk⟩)
    unfold codeBound
    omega
  · rw [subdivision,ite_eq_right hh]
    have short:=Nat.pow_le_pow_right (n:=2) (by decide) (show h≤3 by omega)
    apply le_trans (subdivision_program_size h d)
    exact (Nat.mul_le_mul_left _ short).trans_eq (Nat.mul_comm _ _)

private theorem body_supported (h d : ℕ) (j : Fin (rounds d)) : Supported (body h d j) := by
  unfold body
  apply Supported.seq
  · apply Supported.seq
    · exact @Supported.mk (ramWidth h d) (stage h d j) (@stage_cheap h d j)
    · exact record_good _ _ _ _
  · exact @Supported.mk (ramWidth h d) (unstage h d j) (@unstage_cheap h d j)

private theorem level_supported (h d j : ℕ) : Supported (level h d j) := by
  unfold level
  split
  next good =>
    apply Supported.seq
    · apply Supported.seq
      · exact schedule_good _ _
      · let bodyHere := body h d ⟨j,good⟩
        exact @Supported.mk (ramWidth h d) (CompactLoop.program h bodyHere)
          (@CompactLoop.cheap (ramWidth h d) h bodyHere
            (@Supported.code (ramWidth h d) bodyHere (body_supported h d ⟨j,good⟩)))
    · exact schedule_good _ _
  next => exact schedule_good _ _

theorem subdivision_cheap (h d : ℕ) : CheapCode (subdivision h d) := by
  have supported : Supported (subdivision h d) := by
    unfold subdivision
    split
    · exact chronological_good (schedule_good _ (rootPasses h)) (level_supported h d) (rounds d)
    · exact @Supported.mk (ramWidth h d) (subdivisionProgram h d) (@Native.subdivision_cheap h d)
  intro P R K pc reg pub exit rowIndex
  exact Supported.code supported pc reg pub exit rowIndex

end
end Hierarchy.ProbeStage.Native.Compact

end OAI

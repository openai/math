import OAI.Hierarchy.ProbeStageProgram
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # The subdivision machine uses the linear-cost word instructions -/

namespace Hierarchy.ProbeStage.Native
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr PhysicalPinsExpr

private def basic {n : ℕ} : Formula n → Prop
  | .reg _ | .lit _ | .param _ => True
  | .op op x y => allowed op ∧ basic x ∧ basic y
  | .cut x y => basic x ∧ basic y
  | .load x => basic x
  | .select _ x y a b => basic x ∧ basic y ∧ basic a ∧ basic b

private theorem closed_good {n w k : ℕ} (f : Formula n) (hf : basic f) :
    admissible (AdmissionBank.closed f : Term w k n) := by
  induction f <;> simp_all [AdmissionBank.closed,basic,Term.select,Term.load,Term.binary,Term.literal,
    admissible_let,admissible_rename,admissible,opAllowed,allowed]

private theorem put_good {w a : ℕ} {f : Formula 1} (hf : basic f) :
    CheapCode (WordStore.put w a f) :=
  writing_cheap _ _ _ _ (closed_good _ hf)

private theorem scatter_good {w : ℕ} (v : MaskUpdate.Parameters w) :
    CheapCode (MaskUpdate.procedure v) := by
  intro P R K pc reg pub exit i
  change Fin (4+MaskUpdate.ops.length) at i
  fin_cases i <;> trivial

private theorem store_good (w ptr val : ℕ) : CheapCode (RankUpdate.store w ptr val) := by
  intro P R K pc reg pub exit i
  change Fin 5 at i
  fin_cases i <;> trivial

private theorem rank_good (w : ℕ) (s : RankUpdate.Layout) : CheapCode (RankUpdate.procedure w s) := by
  unfold RankUpdate.procedure
  refine cheap_seq (put_good ?_) (cheap_seq (put_good ?_) (cheap_seq (put_good ?_)
    (cheap_seq (store_good w s.ptr s.value) (cheap_seq (put_good ?_) (cheap_seq (put_good ?_)
      (scatter_good (RankUpdate.page w s)))))))
  all_goals simp [RankUpdate.pointer,RankUpdate.getRank,RankUpdate.increment,RankUpdate.directory,
    RankUpdate.activation,RankUpdate.cell,basic,allowed]

private theorem counted_good {w : ℕ} {p : Procedure w} (s : Word w) (hp : CheapCode p) :
    CheapCode (p.counted s) := by
  intro P R K pc reg pub exit i
  change Fin (7+p.labels) at i
  induction i using Fin.addCases with
  | left j =>
    simp only [Procedure.counted,CompressorIteration.block,Fin.addCases_left]
    fin_cases j <;> trivial
  | right j =>
    simp only [Procedure.counted,CompressorIteration.block,ContinuationLink.Block.reindex,Fin.addCases_right]
    exact hp _ _ _ _ j

private theorem fallback_good (w : ℕ) (s : Fallback.Layout) : CheapCode (Fallback.procedure w s) := by
  apply counted_good
  apply put_good
  simp [Fallback.update,Fallback.count,Fallback.cell,basic,allowed]

private theorem fast_good (w : ℕ) (s : FastField.Layout) : CheapCode (FastField.procedure w s) := by
  apply put_good
  suffices good : ∀ xs : List ℕ, basic (FastField.first s xs) from good _
  intro xs
  induction xs with
  | nil => trivial
  | cons k xs ih => simpa [FastField.first,FastField.common,FastField.wordAt,FastField.cell,basic,allowed] using ih

private theorem chain_good (w : ℕ) (xs : List Record.Write) (tail : Procedure w)
    (terms : ∀ x∈xs,basic x.val) (next : CheapCode tail) : CheapCode (Record.chain w xs tail) := by
  induction xs with
  | nil => exact next
  | cons a xs ih =>
    exact cheap_seq (put_good (terms a (by simp))) (ih (fun x hx => terms x (by simp [hx])))

private structure Supported {w : ℕ} (p : Procedure w) : Prop where
  code : CheapCode p

private theorem Supported.seq {w : ℕ} {a b : Procedure w} (x : Supported a) (y : Supported b) :
    Supported (a.seq b) := ⟨@cheap_seq w a b x.code y.code⟩

private theorem Supported.chain {w : ℕ} (xs : List Record.Write) {p : Procedure w}
    (terms : ∀ x∈xs,basic x.val) (tail : Supported p) : Supported (Record.chain w xs p) :=
  ⟨chain_good w xs p terms tail.code⟩

private theorem rank_supported (w : ℕ) (s : RankUpdate.Layout) : Supported (RankUpdate.procedure w s) :=
  ⟨@rank_good w s⟩

private theorem fallback_supported (w : ℕ) (s : Fallback.Layout) : Supported (Fallback.procedure w s) :=
  ⟨@fallback_good w s⟩

private theorem record_good (w : ℕ) (a : Record.Advice) (s : Record.Scratch) (r : Record.Row) :
    Supported (Record.procedure w a s r) := by
  unfold Record.procedure
  apply Supported.chain
  · intro x hx
    simp only [Record.prepare,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [RankUpdate.directory,RankUpdate.cell,basic,allowed]
  · apply Supported.seq (⟨fast_good w (Record.find a s)⟩ : Supported (FastField.procedure w (Record.find a s)))
    apply Supported.chain
    · intro x hx
      simp only [Record.start,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl <;> simp [Record.miss,RankUpdate.cell,basic,allowed]
    · exact (fallback_supported w (Record.fallback a r s)).seq
        ((rank_supported w (Record.side a r s true)).seq (rank_supported w (Record.side a r s false)))

private theorem chronological_good {w : ℕ} {first : Procedure w} {row : ℕ → Procedure w}
    (initial : Supported first) (good : ∀ i, Supported (row i)) (count : ℕ) :
    Supported (chronological first row count) := by
  induction count with
  | zero => exact initial
  | succ k ih => exact ih.seq (good k)

private theorem schedule_good (w : ℕ) (rows : List Pass) : Supported (program w rows) :=
  ⟨program_cheap w rows⟩

private theorem level_good (h d j : ℕ) : Supported (oneLevel h d j) := by
  unfold oneLevel
  apply Supported.seq
  · apply chronological_good (schedule_good _ _)
    intro i
    exact record_good _ _ _ _
  · exact schedule_good _ _

/-- Every instruction in the literal subdivision program has a linear-width tagged implementation. -/
theorem subdivision_cheap (h d : ℕ) : CheapCode (subdivisionProgram h d) :=
  (chronological_good (schedule_good _ (rootPasses h)) (level_good h d) (rounds d)).code

end Hierarchy.ProbeStage.Native

end OAI

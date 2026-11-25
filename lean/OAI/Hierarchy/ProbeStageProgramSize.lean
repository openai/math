import OAI.Hierarchy.ProbeStageProgram

namespace OAI
/-! # Linear instruction, register, and public-word counts of the native subdivision -/

namespace Hierarchy.ProbeStage.Native
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr PhysicalPinsExpr
open scoped BigOperators

def text {w : ℕ} (p : Procedure w) := p.labels+p.registers+p.slots

theorem text_seq {w : ℕ} (a b : Procedure w) : text (a.seq b)=text a+text b := by
  simp only [Procedure.seq,text]
  omega

private theorem text_put (w addr : ℕ) (f : Formula 1) : text (WordStore.put w addr f)=11+4*f.work := by
  simp [WordStore.put,PhysicalInputPhases.writing,text,Term.labels_eq,AdmissionBank.binds_closed]
  omega

private theorem rank_text (w : ℕ) (s : RankUpdate.Layout) : text (RankUpdate.procedure w s)≤1000 := by
  simp only [RankUpdate.procedure,text_seq,text_put]
  norm_num [RankUpdate.pointer,RankUpdate.getRank,RankUpdate.increment,RankUpdate.directory,
    RankUpdate.activation,RankUpdate.cell,RankUpdate.store,MaskUpdate.procedure,MaskUpdate.ops,Formula.work,text]

private theorem fallback_text (w : ℕ) (s : Fallback.Layout) : text (Fallback.procedure w s)≤1000 := by
  have counted (p : Procedure w) (c : Word w) : text (p.counted c)=10+text p := by
    simp only [Procedure.counted,text]
    omega
  rw [Fallback.procedure,counted,text_put]
  norm_num [Fallback.update,Fallback.count,Fallback.cell,Formula.work]

private theorem record_text (w : ℕ) (a : Record.Advice) (s : Record.Scratch) (r : Record.Row) :
    text (Record.procedure w a s r)≤5000+164*a.chunks := by
  have fast : text (FastField.procedure w (Record.find a s))=15+164*a.chunks := by
    rw [FastField.procedure,text_put,FastField.work]
    change 11+4*(1+41*a.chunks)=_
    ring
  have left := rank_text w (Record.side a r s true)
  have right := rank_text w (Record.side a r s false)
  have slow := fallback_text w (Record.fallback a r s)
  simp only [Record.procedure,Record.prepare,Record.start,Record.chain,text_seq,text_put,fast]
  simp only [RankUpdate.directory,RankUpdate.cell,Record.miss,Formula.work]
  omega

theorem columns_text (w n base work : ℕ) (es : List Expr) (small : ∀ e∈es,e.work≤work) :
    text (program w (columns n base es)) ≤ 15+es.length*(11+4*work) := by
  induction es generalizing base with
  | nil =>
    have size := program_size w []
    simp [columns,text,size.1,size.2.1,size.2.2]
  | cons e es ih =>
    have hs := scan_size w base n e
    have sm := small e (.head _)
    have tail := ih (base+n) (fun t ht => small t (.tail _ ht))
    have head : text (scan w base n e)≤11+4*work := by
      simp only [text,hs.1,hs.2.1,hs.2.2]
      omega
    change text ((scan w base n e).seq (program w (columns n (base+n) es)))≤_
    rw [text_seq,List.length_cons,Nat.succ_mul]
    omega

private theorem walk_text {w : ℕ} (initial : Procedure w) (row : ℕ → Procedure w) (n C : ℕ)
    (small : ∀ i<n,text (row i)≤C) :
    text (chronological initial row n)≤text initial+n*C := by
  induction n with
  | zero => simp [chronological]
  | succ n ih =>
    rw [chronological,text_seq,Nat.succ_mul]
    exact (add_le_add (ih (fun i hi => small i (Nat.lt_succ_of_lt hi))) (small n (Nat.lt_succ_self _))).trans_eq
      (by omega)

private theorem level_text (h d j : ℕ) : text (oneLevel h d j) ≤ 15000*2^h := by
  let w := wordBits h d copies
  let x := endpointAt h d copies j
  have pre := columns_text w (2^h) (allocatorBase h d copies j) 32 (List.ofFn x.term) (by
    intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact x.work i)
  let o := operandsAt h d copies j
  let t := tablesAt h d copies j
  have post := columns_text w (2^h) (output h d copies j) 32 (List.ofFn (field o t)) (by
    intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact field_work o t i)
  simp only [List.length_ofFn] at pre post
  have rows := walk_text (program w (prepareRows h d j)) (visit h d j) (2^h) 12872 (by
    intro i hi
    have item := record_text w (recordAdvice h d j) (recordScratch h d j) (recordRow h d j i)
    change text (visit h d j i)≤5000+164*fieldChunks h at item
    have chunks := (chunks_cover h).2.2
    omega)
  change text (program w (prepareRows h d j))≤_ at pre
  change text (program w (writeRows h d j))≤_ at post
  rw [oneLevel,text_seq]
  dsimp only [w] at rows pre post
  have positive := Nat.two_pow_pos h
  omega

theorem subdivision_program_size (h d : ℕ) :
    text (subdivisionProgram h d)≤(53+15000*rounds d)*2^h := by
  let w:=wordBits h d copies
  have root := columns_text w (2^h) (2^h) 2 ([.lit 0,.row] : List Expr) (by simp [Expr.work])
  change text (program w (rootPasses h))≤53 at root
  have whole := walk_text (program w (rootPasses h)) (oneLevel h d) (rounds d) (15000*2^h)
    (fun j _ => level_text h d j)
  have n := Nat.two_pow_pos h
  calc
    _ ≤ text (program w (rootPasses h)) + rounds d*(15000*2^h) := whole
    _ ≤ 53*2^h + rounds d*(15000*2^h) := Nat.add_le_add_right (by omega) _
    _ = _ := by ring

end Hierarchy.ProbeStage.Native

end OAI

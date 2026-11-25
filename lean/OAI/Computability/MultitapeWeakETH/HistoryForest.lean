import OAI.Computability.MultitapeWeakETH.HistoryVisitChildren
import OAI.Computability.MultitapeWeakETH.WitnessPushNames

/-! # Following a chronological branch through the factor expansion -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression CompressorRecords NetworkKernel PairSimulation LocalHistory
open NodeArguments TreeDecode WitnessWalk
open private collectLevels from OAI.Computability.VPVNP.CompressorExecutionLevels
open private castParsers from OAI.Computability.VPVNP.PairSimulationAssemblyBounds
open scoped Classical
noncomputable section

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
    {hist : ℕ} (order : B.Entry ≃ Fin hist) {f : B.Entry → R} {hf : B.IsSolution f}
    (visit : Visit VisitContext) (ctx : VisitContext)

def LayerStep (first : ℕ) (V : SelectedLevel B f hf) :=
  NodeSpec order visit ctx (originReader B f hf V.origin V.term) (inputJob V.input first) (outputJob V first)

def LayerSteps : ℕ → List (SelectedLevel B f hf) → Prop
  | _, [] => True
  | first,V::vs => LayerStep order visit ctx first V ∧ LayerSteps (first+1) vs

theorem layerSteps_of_index {first : ℕ} (vs : List (SelectedLevel B f hf))
    (h : ∀ i : Fin vs.length, LayerStep order visit ctx (first+i.val) vs[i.val]) : LayerSteps order visit ctx first vs := by
  induction vs generalizing first with
  | nil => trivial
  | cons v vs ih =>
    have head := h ⟨0,by simp⟩
    refine ⟨head,ih (fun i => ?_)⟩
    have tail := h ⟨i.val+1,by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using i.isLt⟩
    simpa only [List.getElem_cons_succ,Nat.add_right_comm first 1 i.val,Nat.add_assoc] using tail

private def pullJob {N M : Network} (e : N=M) (job : SiteJobs M) : SiteJobs N := by cases e; exact job

private theorem pull_job {N M : Network} (e : N = M) (level : ℕ) (o : Order M.Site) (pack : ∀ u, M.Half u → Bits.Word) :
    (fun u h => ((tally level,tally (((e.symm ▸ o : Order N.Site).entries.symm u).val)),pullBits e pack u h)) =
      pullJob e (fun u h => ((tally level,tally (o.entries.symm u).val),pack u h)) := by cases e; rfl

private theorem step_output (V : SelectedLevel B f hf) (level : ℕ) :
    outputJob V level = pullJob (V.pass.output_eq V.term) (inputJob (V.pass.next V.term) (level+1)) :=
  pull_job (V.pass.output_eq V.term) _ (siteOrder (V.pass.next V.term)) (packed (V.pass.next V.term))

private theorem pass_eq {N M Y : Network} (e : N=M) (c : TermChain R M Y) (r : ChainParsers f c)
    (P : SiteParsers f N) (job : SiteJobs M) (last : SiteJobs Y)
    (atHead : SiteSpec order visit ctx P (pullJob e job))
    (later : ∀ Q, SiteSpec order visit ctx Q job → SiteSpec order visit ctx (finalParsers c r Q) last) :
    SiteSpec order visit ctx (finalParsers (e.symm ▸ c) (castParsers e.symm c r) P) last := by
  cases e
  exact later P atHead

set_option maxHeartbeats 1200000 in
theorem branch_forest {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (W : E.MapWitnesses f) (rd : ExecutionReaders E W) (orig : PassOrigins B f hf E) (rec : E.Records) (z : E.Choices)
    (matchers : ReaderOrigins B f hf E W rd orig) (first : ℕ) :
    let passes := collectLevels B f hf E W rd orig z
    LayerSteps order visit ctx first passes → ∀ P : SiteParsers f X.network,
      SiteSpec order visit ctx P (inputJob X first) →
      SiteSpec order visit ctx (finalParsers (E.termChain rec z) (branchParsers E W rd rec z) P)
        (inputJob (E.finalState z) (first+passes.length)) := by
  induction E generalizing first with
  | done => intro _ _ _ h; exact h
  | @more a g b' n' X pass tail ih =>
    intro passes steps P start
    let V : SelectedLevel B f hf := ⟨a,g,b',n',X,pass,orig.1,z.1,rd.1.select.encode z.1⟩
    let rest := collectLevels B f hf (tail z.1) (W.2 z.1) (rd.2 z.1) (orig.2 z.1) z.2
    change LayerStep order visit ctx first V ∧ LayerSteps order visit ctx (first+1) rest at steps
    have head := steps.1
    change NodeSpec order visit ctx (originReader B f hf orig.1 z.1) (inputJob X first) (outputJob V first) at head
    rw [← matchers.1 z.1] at head
    have pushed := SiteSpec.push order visit ctx _ P start head
    rw [step_output] at pushed
    have later := ih z.1 (W.2 z.1) (rd.2 z.1) (orig.2 z.1) (rec.2 z.1) z.2 (matchers.2 z.1) (first+1) steps.2
    have len : first+passes.length = first+1+rest.length := by change first+(rest.length+1) = _; omega
    rw [len]
    exact pass_eq order visit ctx (pass.output_eq z.1) _ _ _ _ _ pushed later

end
end OAI.Computability.MultitapeWeakETH.NativeGrid

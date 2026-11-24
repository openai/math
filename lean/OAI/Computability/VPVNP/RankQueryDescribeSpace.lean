import OAI.Computability.VPVNP.RankQueryDescribeAdapter
import OAI.Computability.VPVNP.RankQueryGramScalarSpace
import OAI.Computability.VPVNP.RankQueryRoutineSpace

/-! # Independent time and space bounds for the Schur description action -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.DescribeAdapter

open RAMTape BurstRAM Dispatch Engine UniversalCountStack

variable {K : Type} [DecidableEq K] {p e n m w v d U Z A S B T : ℕ} [Fact p.Prime] [NeZero e]
  {c : SliceArithmetic.Vector p e}

/-- A local call's per-port peak as a function of the initial height. -/
def CallSpace (call : Bool → FiniteRoutine (GramScalar.Port K)) (entry : Entry n (Scalar c))
    (w v m d T : ℕ) (peak : ℕ → ℕ) (ready : Stacks K → Prop) : Prop :=
  ∀ {A : ℕ} (i j : Fin n) (z : ℕ) (neg : Bool) (persist : Word w) (rs : GramScalar.Registers w),
    (∀ a, gramInput i j z m a < 2^d) → (∀ a, (rs (Code.inReg capacity a)).val = gramInput i j z m a) →
    ∀ s : Stacks K, ready s →
    (∀ a, (GramScalar.bank (GramScalar.wordBank persist rs) (GramRead.arithmeticBank v c [] []) s a).length ≤ A) →
    ∃ t ≤ T, ∃ rs' out, ready out ∧ (∀ a, rs' (Code.inReg capacity a) = rs (Code.inReg capacity a)) ∧
      (call neg).BoundedRun (peak A) t
        (GramScalar.bank (GramScalar.wordBank persist rs) (GramRead.arithmeticBank v c [] []) s)
        (GramScalar.bank (GramScalar.wordBank persist rs')
          (GramRead.arithmeticBank v c [] (scalar v (if neg then -entry i j z else entry i j z))) out)

omit [NeZero e] in
theorem value_bounded (call : Bool → FiniteRoutine (GramScalar.Port K)) (entry : Entry n (Scalar c))
    {ready : Stacks K → Prop} {peak : ℕ → ℕ} (hc : CallRuns call entry w v m d T ready)
    (hspace : CallSpace call entry w v m d T peak ready) (hpeak : A ≤ peak A)
    (hd : d ≤ w) (i j : Fin n) (z : ℕ) (neg : Bool) (live saved : Data) (aux : Stacks (Aux K))
    (haux : RightReady w v m c ready aux) (he : ∀ a, gramInput i j z m a < 2^d)
    (hdesc : ∀ a : Fin 3, aux (.inl (outputSlot ⟨a.val+1,by omega⟩)) =
      UniversalCountStack.digits w (gramInput i j z m ⟨a.val,by omega⟩))
    (start : ∀ k, (store live saved [] [] aux k).length ≤ A) :
    ∃ t ≤ T, ∃ out, RightReady w v m c ready out ∧ (∀ x, out (.inl x) = aux (.inl x)) ∧
      (valueRoutine call neg).BoundedRun (peak A) t (store live saved [] [] aux)
        (store live saved [] (scalar v (if neg then -entry i j z else entry i j z)) out) := by
  obtain ⟨t,ht,out,hready,hsame,hrun⟩ := value_runs call entry hc hd i j z neg live saved aux haux he hdesc
  obtain ⟨base,persist,localBank,hparams,hlocal,hs⟩ := haux
  obtain ⟨hreg,hin⟩ := prepare i j z live saved aux base persist localBank hparams hs hd he hdesc
  obtain ⟨_,_,_,_,_,_,hb⟩ := hspace i j z neg persist _ he hreg localBank hlocal (fun k => hin k ▸ start (gramPorts k))
  exact ⟨t,ht,out,hready,hsame,hb.lift_trace gramPorts_injective hrun (fun k => (start k).trans hpeak) hin⟩

/-- Bound on each stack during description from initial height `A`. The local coefficient call
uses `peak` after the descriptor program, with additional room for clearing, copying and
writing a literal. -/
def peakWith (w v e A : ℕ) (peak : ℕ → ℕ) := peak (A+Operation.describe.clock w) + (10*(w+1)+2) + 7*(e*v)+3 + (5*w+3)

/-- Peak stack height for a Schur description with signed Gram entries, using `A` for initial
height and `S` for each matrix-entry read. -/
def space (w v e A S : ℕ) := peakWith w v e A (fun a => GramScalar.space w v e a S)

/-- A Schur action shares the input bank's height bound across long matrix
reads. The three-bit dispatch and the one-bit Gram tag restore their inputs. -/
theorem describe_entries_bounded (call : Bool → FiniteRoutine (GramScalar.Port K)) (entry : Entry n (Scalar c))
    {ready : Stacks K → Prop} {peak : ℕ → ℕ} (hc : CallRuns call entry w v m d T ready)
    (hspace : CallSpace call entry w v m d T peak ready) (hpeak : ∀ a, a ≤ peak a)
    (hw : SliceArithmetic.Word.workingWidth p ≤ v) (hw₃ : 3 ≤ w) (hp : (d+1)*widthFactor ≤ w) (hd : d ≤ w)
    (hsize : n+U+Z+m+8 < 2^d)
    (q : SchurKey n U Z) (fs : List (F n U Z c)) (aux : Stacks (Aux K)) (hs : Ready w v n m c ready aux)
    (start : ∀ k, (atControl w v (.enter q) fs aux [] k).length ≤ A) :
    ∃ t ≤ timeWith w v e T, ∃ out, Ready w v n m c ready out ∧
      (describeWith call).BoundedRun (peakWith w v e A peak) t (atControl w v (.enter q) fs aux)
        (match (SchurKey.program entry).describe q with
         | .inl r => atControl w v (.returned r) fs out [true]
         | .inr k => atControl w v (.scan q k 0) fs out [false]) := by
  obtain ⟨t,ht,out,hout,whole⟩ := describe_entries call entry hc hw hw₃ hp hd hsize q fs aux hs
  refine ⟨t,ht,out,hout,?_⟩
  let vs := Dispatch.describe.eval (inputs q 0)
  let saved := history w v fs
  let data := fields w [] q [] [] []
  let A₀ := A+Operation.describe.clock w
  let P := peakWith w v e A peak
  have h₀ : A₀ ≤ peak A₀ := hpeak _
  have h₁ : peak A₀ ≤ P := by dsimp [P,peakWith,A₀]; omega
  have bounded (i : Fin 8) : inputs q 0 i < 2^d := by
    have hq (j : Fin 6) : q.words j < 2^d := (q.words_le j).trans_lt (by omega)
    fin_cases i <;> first | exact hq _ | (simp [inputs] <;> omega)
  obtain ⟨t₀,ht₀,mid,_,hstage,words,houtside⟩ :=
    EngineAlias.stageDescribe_runs leftBank q saved [] [] aux hs.1 bounded hd hp
  have stage := spaceRun_of_steps hstage (fun k => Nat.add_le_add (start k) ht₀)
  have hm : RightReady w v m c ready mid := by
    obtain ⟨rs,persist,localBank,hparams,hlocal,hbank⟩ := hs.2
    exact ⟨rs,persist,localBank,hparams,hlocal,fun i => (houtside (.inr i) (fun _ h => by contradiction)).trans (hbank i)⟩
  have hmid (k : Engine.Port (Aux K)) : (atControl w v (.enter q) fs mid [] k).length ≤ peak (A+Operation.describe.clock w) := (stage.final_cap k).trans h₀
  have valid : ValidDescription n Z vs := describe_valid q 0
  have htag : vs 0 < 2^3 := by have := valid.1; omega
  have finish {u : ℕ} {endBank : Stacks (Engine.Port (Aux K))}
      (arm : (entryArm call (vs 0)).BoundedRun P u (atControl w v (.enter q) fs mid) endBank) :
      (describeWith call).BoundedRun P t (atControl w v (.enter q) fs aux)
        (match (SchurKey.program entry).describe q with
         | .inl r => atControl w v (.returned r) fs out [true]
         | .inr k => atControl w v (.scan q k 0) fs out [false]) := by
    have routed := TagRouter.digits_bounded (.aux (.inl (outputSlot 0))) (entryArm call) hw₃ htag _ _ (words 0) arm
    have total := (FiniteRoutine.BoundedRun.enlarge (r := EngineAlias.stageDescribe leftBank) stage (h₀.trans h₁)).followedBy routed
    obtain ⟨eq₁,eq₂⟩ := FiniteRoutine.return_unique total.runs whole
    rw [eq₁,eq₂] at total; exact total
  have casesTag : vs 0 = 4 ∨ vs 0 = 0 ∨ vs 0 = 1 ∨ vs 0 = 2 ∨ vs 0 = 3 := by have := valid.1; omega
  rcases casesTag with h4 | h0 | h1 | hread
  · have ha := Describe.arity_runs hw wires q fs mid (clean hm) (vs 1) (words 1)
    apply finish
    simp only [entryArm,h4,ite_true]
    apply spaceRun_of_steps ha
    intro k; have := hmid k; unfold P peakWith; omega
  · obtain ⟨u,hu,ha⟩ := Describe.terminal_runs (w := w) hw wires q fs mid (clean hm) false
    apply finish
    simp [entryArm,h0]
    apply spaceRun_of_steps ha
    intro k; have := hmid k; unfold P peakWith; omega
  · obtain ⟨u,hu,ha⟩ := Describe.terminal_runs (w := w) hw wires q fs mid (clean hm) true
    apply finish
    simp [entryArm,h1]
    apply spaceRun_of_steps ha
    intro k; have := hmid k; unfold P peakWith; omega
  · obtain ⟨hi,hj,hz⟩ := valid.2 hread
    let i : Fin n := ⟨vs 1,hi⟩
    let j : Fin n := ⟨vs 2,hj⟩
    let neg := decide (vs 0 = 3)
    have he (a : Fin 8) : gramInput i j (vs 3) m a < 2^d := by fin_cases a <;> simp [gramInput,i,j] <;> omega
    have hword (a : Fin 3) : mid (.inl (outputSlot ⟨a.val+1,by omega⟩)) =
        UniversalCountStack.digits w (gramInput i j (vs 3) m ⟨a.val,by omega⟩) := by fin_cases a <;> exact words _
    obtain ⟨_,_,last,_,_,hr⟩ := value_bounded call entry hc hspace h₀ hd i j (vs 3) neg data saved mid hm he hword stage.final_cap
    let r := if neg then -entry i j (vs 3) else entry i j (vs 3)
    obtain ⟨u,hu,hf⟩ := Describe.finish_runs (w := w) (v := v) q fs r last
    have hf' := spaceRun_of_steps hf (fun k => Nat.add_le_add (hr.final_cap k) hu)
    apply finish
    simp only [entryArm,ite_eq_right (show vs 0 ≠ 4 by omega),ite_eq_right (show vs 0 ≠ 0 by omega),
      ite_eq_right (show vs 0 ≠ 1 by omega)]
    exact (hr.enlarge h₁).followedBy (FiniteRoutine.BoundedRun.enlarge (r := Describe.finish) hf' (by dsimp [P,peakWith,A₀]; omega))

theorem describe_bounded (read : FiniteRoutine (MacaulayRead.Port K)) (M : Matrix (Fin n) (Fin m) (Scalar c))
    {ready : Stacks K → Prop} (hc : MacaulayRead.CorrectSpace read M w v B S ready)
    (hw : SliceArithmetic.Word.workingWidth p ≤ v) (hw₃ : 3 ≤ w) (hp : (d+1)*widthFactor ≤ w) (hd : d ≤ w)
    (hsize : n+U+Z+m+8 < 2^d)
    (q : SchurKey n U Z) (fs : List (F n U Z c)) (aux : Stacks (Aux K)) (hs : Ready w v n m c ready aux)
    (start : ∀ k, (atControl w v (.enter q) fs aux [] k).length ≤ A) :
    ∃ t ≤ clock w v e B, ∃ out, Ready w v n m c ready out ∧
      (describe read).BoundedRun (space w v e A S) t (atControl w v (.enter q) fs aux)
        (match (SchurKey.program (weightedGramEntryCoeff M)).describe q with
         | .inl r => atControl w v (.returned r) fs out [true]
         | .inr k => atControl w v (.scan q k 0) fs out [false]) := by
  apply describe_entries_bounded (GramScalar.machine read) (weightedGramEntryCoeff M)
    (GramScalar.machine_runs read M hc.correct hw (by omega) hp)
    (fun {a} => GramScalar.machine_bounded (A := a) read M hc hw (by omega) hp) _ hw hw₃ hp hd hsize q fs aux hs start
  intro a; unfold GramScalar.space; have := le_max_left (a+Operation.gram.clock w) S; omega

end RankQuery.Stack.DescribeAdapter

end VPVNP
end Computability
end OAI

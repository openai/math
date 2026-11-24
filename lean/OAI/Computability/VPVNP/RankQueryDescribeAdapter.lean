import OAI.Computability.VPVNP.RankQueryGramAlias
import OAI.Computability.VPVNP.RankQueryDescribeWords

/-! # Executable Schur description on a Macaulay relation matrix

The engine's describe action reads the current six-field query, evaluates its
fixed decision tree, selects an arm by the actual output tag, and returns
either a packed scalar or the loop counter and a fresh accumulator.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.DescribeAdapter

open Engine RAMTape Dispatch

variable {K : Type} [DecidableEq K]

/-- Interpret a description tag by setting up a recursive sum, returning field zero or one, or
reading a Gram entry with the indicated sign. -/
def entryArm (call : Bool → FiniteRoutine (GramScalar.Port K)) (tag : ℕ) : FiniteRoutine (Engine.Port (Aux K)) :=
  if tag = 4 then Describe.arity wires
  else if tag = 0 then Describe.terminal wires false else if tag = 1 then Describe.terminal wires true
  else (valueRoutine call (decide (tag = 3))).followedBy Describe.finish

/-- Stage the current Schur query, run the description decision tree, and dispatch on its
three-bit tag using the supplied signed-entry routine. -/
def describeWith (call : Bool → FiniteRoutine (GramScalar.Port K)) : FiniteRoutine (Engine.Port (Aux K)) :=
  (EngineAlias.stageDescribe leftBank).followedBy (TagRouter.select (.aux (.inl (outputSlot 0))) 3 (entryArm call))

/-- Describe one Schur query using the physical Gram-entry routine backed by the Macaulay
matrix reader. -/
def describe (read : FiniteRoutine (MacaulayRead.Port K)) := describeWith (GramScalar.machine read)

/-- Step bound for one description dispatch when a signed Gram-entry call costs at most T
steps. -/
def timeWith (w v e T : ℕ) := Operation.describe.clock w + 6 + (T + (10*(w+1)+2) + 7*(e*v)+3 + (5*w+3))

/-- Step bound for the physical description dispatch when each underlying Macaulay entry read
costs at most B steps. -/
def clock (w v e B : ℕ) := timeWith w v e (GramScalar.clock w v e B)

variable {w v d p e n m U Z B : ℕ} [Fact p.Prime] [NeZero e] {c : SliceArithmetic.Vector p e}

omit [DecidableEq K] in
private theorem left_ready {s u : Stacks (Aux K)} (h : EngineAlias.Ready leftBank w n s)
    (same : ∀ x, u (.inl x) = s (.inl x)) : EngineAlias.Ready leftBank w n u := by
  obtain ⟨rs,pers,h₀,hn,hs⟩ := h
  exact ⟨rs,pers,h₀,hn,fun i => (same i).trans (hs i)⟩

omit [DecidableEq K] [Fact p.Prime] [NeZero e] in
private theorem right_ready {ready : Stacks K → Prop} {s u : Stacks (Aux K)} (h : RightReady w v m c ready s)
    (same : ∀ x, u (.inr x) = s (.inr x)) : RightReady w v m c ready u := by
  obtain ⟨rs,pers,bank,h₀,hn,hs⟩ := h
  exact ⟨rs,pers,bank,h₀,hn,fun i => (same i).trans (hs i)⟩

/-- Physical execution contract for the engine's describe action. Its only
matrix-dependent subprogram computes an individual Macaulay entry. -/
theorem describe_entries {T : ℕ} (call : Bool → FiniteRoutine (GramScalar.Port K)) (entry : Entry n (Scalar c))
    {ready : Stacks K → Prop} (hc : CallRuns call entry w v m d T ready)
    (hw : SliceArithmetic.Word.workingWidth p ≤ v) (hw₃ : 3 ≤ w) (hp : (d+1)*widthFactor ≤ w) (hd : d ≤ w)
    (hsize : n+U+Z+m+8 < 2^d)
    (q : SchurKey n U Z) (fs : List (F n U Z c)) (aux : Stacks (Aux K)) (hs : Ready w v n m c ready aux) :
    ∃ t ≤ timeWith w v e T, ∃ out, Ready w v n m c ready out ∧
      (describeWith call).Runs t (atControl w v (.enter q) fs aux)
        (match (SchurKey.program entry).describe q with
         | .inl r => atControl w v (.returned r) fs out [true]
         | .inr k => atControl w v (.scan q k 0) fs out [false]) := by
  let vs := Dispatch.describe.eval (inputs q 0)
  let saved := history w v fs
  let data := fields w [] q [] [] []
  have bounded (i : Fin 8) : inputs q 0 i < 2^d := by
    have hq (j : Fin 6) : q.words j < 2^d := (q.words_le j).trans_lt (by omega)
    fin_cases i <;> first | exact hq _ | (simp [inputs] <;> omega)
  obtain ⟨t₀,ht₀,mid,hm₀,hstage,words,houtside⟩ :=
    EngineAlias.stageDescribe_runs leftBank q saved [] [] aux hs.1 bounded hd hp
  have hm₁ := right_ready hs.2 (fun x => houtside (.inr x) (fun _ hh => by contradiction))
  have hm : Ready w v n m c ready mid := ⟨hm₀,hm₁⟩
  have valid : ValidDescription n Z vs := describe_valid q 0
  have htag : vs 0 < 2^3 := by have := valid.1; omega
  have hdesc : (SchurKey.program entry).describe q = decode entry vs :=
    (describe_eq _ q 0).symm
  rw [hdesc]
  have execute {t : ℕ} {out : Stacks (Engine.Port (Aux K))}
      (h : (entryArm call (vs 0)).Runs t (atControl w v (.enter q) fs mid) out) :
      (describeWith call).Runs (t₀+(2*3+t)) (atControl w v (.enter q) fs aux) out := by
    exact hstage.followedBy (TagRouter.digits_runs _ (entryArm call) hw₃ htag _ _ (words 0) h)
  have casesTag : vs 0 = 4 ∨ vs 0 = 0 ∨ vs 0 = 1 ∨ vs 0 = 2 ∨ vs 0 = 3 := by have := valid.1; omega
  rcases casesTag with h4 | h0 | h1 | hread
  · have ha := Describe.arity_runs hw wires q fs mid (clean hm₁) (vs 1) (words 1)
    refine ⟨t₀+(2*3+((5*w+2)+(7*(e*v)+3)+1)),by unfold timeWith; omega,mid,hm,?_⟩
    simp only [decode,h4,ite_true]
    apply execute
    simpa [entryArm,h4] using ha
  · obtain ⟨t,ht,ha⟩ := Describe.terminal_runs (w := w) hw wires q fs mid (clean hm₁) false
    refine ⟨t₀+(2*3+t),by unfold timeWith; omega,mid,hm,?_⟩
    simp only [decode,h0,ite_false,ite_true,OfNat.zero_ne_ofNat,Nat.zero_ne_one]
    apply execute
    simpa [entryArm,h0,Describe.constant] using ha
  · obtain ⟨t,ht,ha⟩ := Describe.terminal_runs (w := w) hw wires q fs mid (clean hm₁) true
    refine ⟨t₀+(2*3+t),by unfold timeWith; omega,mid,hm,?_⟩
    simp [decode,h1]
    apply execute
    simpa [entryArm,h1,Describe.constant] using ha
  · obtain ⟨hi,hj,hz⟩ := valid.2 hread
    let i : Fin n := ⟨vs 1,hi⟩
    let j : Fin n := ⟨vs 2,hj⟩
    let neg := decide (vs 0 = 3)
    have he (a : Fin 8) : gramInput i j (vs 3) m a < 2^d := by fin_cases a <;> simp [gramInput,i,j] <;> omega
    have hword (a : Fin 3) : mid (.inl (outputSlot ⟨a.val+1,by omega⟩)) =
        UniversalCountStack.digits w (gramInput i j (vs 3) m ⟨a.val,by omega⟩) := by
      fin_cases a <;> exact words _
    obtain ⟨t₁,ht₁,out,hout₁,hleft,hr⟩ := value_runs call entry hc hd i j (vs 3) neg data saved mid hm₁ he hword
    let r := if neg then -entry i j (vs 3) else entry i j (vs 3)
    obtain ⟨t₂,ht₂,hf⟩ := Describe.finish_runs (w := w) (v := v) q fs r out
    have run : (entryArm call (vs 0)).Runs (t₁+t₂) (atControl w v (.enter q) fs mid)
        (atControl w v (.returned r) fs out [true]) := by
      have h₀ : vs 0 ≠ 0 := by omega
      have h₁ : vs 0 ≠ 1 := by omega
      have h₄ : vs 0 ≠ 4 := by omega
      simp only [entryArm,h₄,h₀,h₁,ite_false]
      exact hr.followedBy hf
    have eq : decode entry vs = .inl r := by
      rcases hread with h|h <;> simp [decode,r,neg,h,hi,hj,i,j]
    rw [eq]
    exact ⟨t₀+(2*3+(t₁+t₂)),by unfold timeWith; omega,out,⟨left_ready hm₀ hleft,hout₁⟩,execute run⟩

theorem describe_runs (read : FiniteRoutine (MacaulayRead.Port K)) (M : Matrix (Fin n) (Fin m) (Scalar c))
    {ready : Stacks K → Prop} (hc : MacaulayRead.Correct read M w v B ready)
    (hw : SliceArithmetic.Word.workingWidth p ≤ v) (hw₃ : 3 ≤ w) (hp : (d+1)*widthFactor ≤ w) (hd : d ≤ w)
    (hsize : n+U+Z+m+8 < 2^d)
    (q : SchurKey n U Z) (fs : List (F n U Z c)) (aux : Stacks (Aux K)) (hs : Ready w v n m c ready aux) :
    ∃ t ≤ clock w v e B, ∃ out, Ready w v n m c ready out ∧
      (describe read).Runs t (atControl w v (.enter q) fs aux)
        (match (SchurKey.program (weightedGramEntryCoeff M)).describe q with
         | .inl r => atControl w v (.returned r) fs out [true]
         | .inr k => atControl w v (.scan q k 0) fs out [false]) :=
  describe_entries (GramScalar.machine read) (weightedGramEntryCoeff M)
    (GramScalar.machine_runs read M hc hw (by omega) hp) hw hw₃ hp hd hsize q fs aux hs

end RankQuery.Stack.DescribeAdapter

end VPVNP
end Computability
end OAI

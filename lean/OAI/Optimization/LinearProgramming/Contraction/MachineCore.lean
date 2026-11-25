import OAI.Optimization.LinearProgramming.RAM.Code
import OAI.Optimization.LinearProgramming.Contract.AppOracleMachine

/-! ## Running certified scalar RAM blocks inside the arithmetic-oracle machine

The ordinary block executes every original instruction, with the oracle transcript untouched.
Only calls to the genuine `query` instruction may add records. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Contraction
namespace Machine

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.Contract

/-- Erase the oracle instruction into a halt. Every run that ends live therefore stayed
entirely inside ordinary scalar instructions. This view is used only in the simulation proof. -/
def coreView (p : OracleProgram) : Program := p.map fun
  | .core i => i
  | .query .. => .halt 0

/-- The structured RAM block occupies its actual slice inside the larger oracle program. -/
def CoreAt (p : OracleProgram) (pc : ℕ) (body : List Instr) : Prop :=
  ∃ before after, before.length = pc ∧ p = before ++ body.map OracleInstr.core ++ after

theorem CoreAt.view {p : OracleProgram} {pc : ℕ} {body : List Instr} (h : CoreAt p pc body) :
    CodeAt (coreView p) pc body := by
  obtain ⟨pre,post,hlen,rfl⟩ := h
  exact ⟨coreView pre, coreView post, by simpa [coreView] using hlen, by simp [coreView, List.map_map, Function.comp_def]⟩

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem live_before {p : Program} {s t : State K} (h : step p s = some t) :
    s.output = none := by
  cases hs : s.output with
  | none => rfl
  | some tag => simp [step,hs] at h

private theorem live_initial {p : Program} {s t : State K} {k : ℕ} {P : State K → Prop}
    (h : Execution p P s k t) (ht : t.output = none) : s.output = none := by
  cases h with
  | done => exact ht
  | next _ hs _ => exact live_before hs

private theorem oracleStep_of_core {p : OracleProgram} {s t : State K} (o : ScalarOracle K)
    (hist : Contract.History K) (h : step (coreView p) s = some t) (ht : t.output = none) :
    oracleStep p o ⟨s,hist⟩ = some (1,⟨t,hist⟩) := by
  have hs := live_before h
  cases hpc : p[s.pc]? with
  | none => simp [coreView,step,hs,hpc] at h
  | some instr =>
    cases instr with
    | core i =>
      have he : execInstr i s = some t := by simpa [coreView,step,hs,hpc] using h
      simp [oracleStep, hs, hpc, he]
    | query a b c d =>
      have he : {s with output := some 0} = t := by simpa [coreView,step,hs,hpc,execInstr] using h
      subst t
      simp at ht

/-- Embed any live ordinary execution in an arbitrary surrounding oracle program;
the entire raw history and exact number of steps are preserved. -/
theorem lift_execution {p : OracleProgram} {s t : State K} {P : State K → Prop} {k : ℕ}
    (o : ScalarOracle K) (hist : Contract.History K) (h : Execution (coreView p) P s k t)
    (ht : t.output = none) : OracleRun p o ⟨s,hist⟩ k ⟨t,hist⟩ := by
  induction h with
  | done => exact .refl _
  | next _ hs rest ih =>
    simpa only [Nat.one_add] using OracleRun.next (oracleStep_of_core o hist hs (live_initial rest ht)) (ih ht)

/-- Standard assembler loops and branches are reusable unchanged at any offset between real
oracle calls. Machine code and running time are those of the assembled block. -/
theorem run_compiled_block {p : OracleProgram} {pc k : ℕ} {P : Memory K → Prop}
    {body : Block} {m t : Memory K} (o : ScalarOracle K) (hist : Contract.History K)
    (code : CoreAt p pc (body.compile pc)) (work : body.Eval P m k t) :
    OracleRun p o ⟨m.atPC pc,hist⟩ k ⟨t.atPC (pc+body.size),hist⟩ :=
  lift_execution o hist (work.compile_correct code.view) rfl

theorem append_run {p : OracleProgram} {o : ScalarOracle K} {s t u : Config K} {k l : ℕ}
    (first : OracleRun p o s k t) (rest : OracleRun p o t l u) : OracleRun p o s (k+l) u := by
  induction first with
  | refl => simpa using rest
  | next h _ ih => simpa only [Nat.add_assoc] using OracleRun.next h (ih rest)

end Machine
end Contraction
end LinearProgramming
end Optimization
end OAI

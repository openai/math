import OAI.Computability.VPVNP.RAMProcessorGraph

/-!
# Runs to graph exits and to literal rejecting rows

Some budget and format checks reject inside a routine. A rejection witness
retains the exact stopping control and proves its physical row halts false.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

variable {K L Q J : Type}

/-- A deterministic run ending on a rejecting stack instruction. -/
abbrev RejectRun [DecidableEq K] (code : StackCode K Q) (n : ℕ) (q : Q) (s : Stacks K) :=
  ∃ z u, StackRuns code n q s z u ∧ code z = .halt false

theorem StackRuns.thenReject [DecidableEq K] {code : StackCode K Q} {m n q s q' u}
    (h : StackRuns code m q s q' u) (hr : RejectRun code n q' u) :
    RejectRun code (m+n) q s := by
  obtain ⟨z, v, run, halt⟩ := hr
  exact ⟨z, v, h.trans run, halt⟩

theorem Fragment.runs_framed [DecidableEq K] [DecidableEq J] {f : Fragment K L} {ports : K → J}
    (hi : Function.Injective ports) {t st x l y u} (h : f.Runs t x l y)
    (hin : ∀ k, st (ports k) = x k) (hout : ∀ k, u (ports k) = y k)
    (frame : ∀ j, (∀ k, ports k ≠ j) → u j = st j) :
    (f.onPorts ports).Runs t st l u := by
  have hr := f.runs_onPorts ports hi st h
  rwa [installStacks_eq hi st x hin, installStacks_frame hi hout frame] at hr

namespace Fragment

/-- A fragment run that reaches an internal rejecting halt. -/
abbrev Rejects [DecidableEq K] (f : Fragment K L) (n : ℕ) (s : Stacks K) :=
  ∃ q u, StackRuns f.isolated n (.inl f.entry) s (.inl q) u ∧ f.code q = .halt false

theorem returning_reject [DecidableEq K] {r : FiniteRoutine K} {next : L}
    {t q s u} (h : StackRuns r.body.standalone t (some r.body.entry) s (some q) u)
    (bad : r.body.code q = .halt false) : (returning r next).Rejects t s := by
  let labels : Option r.State → (returning r next).State ⊕ L :=
    fun q => q.elim (.inr next) Sum.inl
  have hrow (q : Option r.State) (hc : (r.body.standalone q).returns = false) :
      (returning r next).isolated (labels q) = (r.body.standalone q).rename id labels := by
    cases q with | none => contradiction | some _ => rfl
  have run := h.lift id Function.injective_id labels s hrow
  have same (a : Stacks K) : installStacks id s a = a := by
    funext j; exact installStacks_at Function.injective_id s a j
  rw [same, same] at run
  exact ⟨q, u, run, by simp [returning, bad]⟩

theorem reject_onPorts [DecidableEq K] [DecidableEq J] {f : Fragment K L} {ports : K → J}
    (hi : Function.Injective ports) {t x st} (h : f.Rejects t x)
    (hin : ∀ i, st (ports i) = x i) : (f.onPorts ports).Rejects t st := by
  obtain ⟨q, u, run, bad⟩ := h
  have hr := run.lift ports hi id st (target := (f.onPorts ports).isolated) (by
    intro q hc; cases q with | inl _ => rfl | inr _ => contradiction)
  rw [installStacks_eq hi st _ hin] at hr
  exact ⟨q, _, hr, by simp [onPorts, bad]⟩

end Fragment

namespace ProcessorFlow

theorem reject [DecidableEq K] {blocks : L → Fragment K L} {l t s}
    (h : (blocks l).Rejects t s) : RejectRun (program blocks) t (enter blocks l) s := by
  obtain ⟨q, u, run, bad⟩ := h
  have hr := run.lift id Function.injective_id (next blocks l) s (target := program blocks) (by
    intro q hc; cases q with | inl _ => rfl | inr _ => contradiction)
  have same (a : Stacks K) : installStacks id s a = a := by
    funext j; exact installStacks_at Function.injective_id s a j
  rw [same, same] at hr
  exact ⟨⟨l,q⟩, u, hr, by simp [program, bad]⟩

theorem routine_reject [DecidableEq K] [DecidableEq J] {blocks : L → Fragment J L}
    {r : FiniteRoutine K} {l next : L} {ports : K → J} (hi : Function.Injective ports)
    (link : blocks l = (Fragment.returning r next).onPorts ports)
    {t q s u st} (h : StackRuns r.body.standalone t (some r.body.entry) s (some q) u)
    (bad : r.body.code q = .halt false) (hin : ∀ i, st (ports i) = s i) :
    RejectRun (program blocks) t (enter blocks l) st := by
  apply reject
  rw [link]
  exact Fragment.reject_onPorts hi (Fragment.returning_reject h bad) hin

end ProcessorFlow
end RAMTape

end VPVNP
end Computability
end OAI

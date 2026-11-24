import OAI.Computability.VPVNP.RankQueryStackEngineRun
import OAI.Computability.VPVNP.RoutineSpace

/-! # Polynomial stack space with expensive scalar-entry calls

The descriptor can invoke another complete matrix or coefficient computation.
Its time may be exponential while its space stays polynomial. The execution
below links its bounded run directly. The other Schur actions have polynomial
instruction budgets and reuse the same workspace between transitions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Engine

open RAMTape UniversalCountStack

variable {n U Z p e : ℕ} {c : SliceArithmetic.Vector p e} {K : Type} [DecidableEq K]
variable [Fact p.Prime] [NeZero e]
variable {a : Actions K} {prog : Program (Key n U Z) (Scalar c)} {w v B Bd lim A d S : ℕ}
variable {ready : Stacks K → Prop} {pending : Key n U Z → Stacks K → Prop}

/-- Scalar reads in the descriptor have independent time and space bounds.
The caller's suspended frames are present throughout the subcall. -/
def DescribeBounded (a : Actions K) (prog : Program (Key n U Z) (Scalar c)) (w v Bd S depth : ℕ)
    (ready : Stacks K → Prop) : Prop := ∀ (q : Key n U Z) (fs : List (F n U Z c)) (aux : Stacks K),
  fs.length ≤ depth → ready aux → ∃ t ≤ Bd, ∃ out, ready out ∧
    a.describe.BoundedRun S t (atControl w v (.enter q) fs aux)
      (match prog.describe q with
       | .inl r => atControl w v (.returned r) fs out [true]
       | .inr k => atControl w v (.scan q k 0) fs out [false])

/-- The descriptor subcall and the short local transitions share the same tapes. -/
def boundedSpace (S A depth B w v e : ℕ) := max (S+1) (runSpace A depth B w v e)

/-- Maximum one-step time allowance covering descriptor evaluation and the other engine
transitions. -/
def boundedStepTime (Bd B w v e : ℕ) := max (Bd+1) (stepBudget B w v e)

omit [Fact p.Prime] [NeZero e] in
private theorem clearSignal (w v : ℕ) (q : Ctl n U Z c) (fs : List (F n U Z c))
    (out : Stacks K) (b : Bool) :
    Function.update (atControl w v q fs out [b]) .condition [] = atControl w v q fs out := by
  funext k
  cases k with
  | frame j => cases j <;> rfl
  | _ => rfl

private theorem step_bounded (spec : Contracts a prog w v B lim ready pending Bd)
    (desc : DescribeBounded a prog w v Bd S d ready) (ha : ∀ s, ready s → ∀ k, (s k).length ≤ A)
    (cfg : Cfg n U Z c) (depth : cfg.2.length ≤ d) (range : InRange lim cfg) (cursor : CursorRange prog cfg)
    (aux : Stacks K) (haux : ready aux) :
    ∃ t ≤ boundedStepTime Bd B w v e, ∃ out, ready out ∧
      SpaceRun (routine a).standalone (boundedSpace S A d B w v e) t
        (some (label a cfg.1)) (atControl w v cfg.1 cfg.2 aux)
        (some (label a (prog.step cfg).1)) (atControl w v (prog.step cfg).1 (prog.step cfg).2 out) := by
  have short (h : (match cfg.1 with | .enter _ => Bd+1 | _ => stepBudget B w v e) = stepBudget B w v e) :
      ∃ t ≤ boundedStepTime Bd B w v e, ∃ out, ready out ∧
        SpaceRun (routine a).standalone (boundedSpace S A d B w v e) t
          (some (label a cfg.1)) (atControl w v cfg.1 cfg.2 aux)
          (some (label a (prog.step cfg).1)) (atControl w v (prog.step cfg).1 (prog.step cfg).2 out) := by
    obtain ⟨t, ht, out, ho, run⟩ := step_runs_separate spec cfg range cursor aux haux
    have hshort : t ≤ stepBudget B w v e := by
      cases cEq : cfg.1 <;> simp only [cEq] at ht h <;> omega
    have bounded := spaceRun_of_steps (cap := runSpace A d B w v e) run (fun k ↦
      Nat.add_le_add (state_length cfg depth aux (ha aux haux) k) hshort)
    exact ⟨t, hshort.trans (le_max_right ..), out, ho, bounded.mono_cap (le_max_right ..)⟩
  obtain ⟨ctl, fs⟩ := cfg
  cases ctl with
  | scan | returned => exact short rfl
  | enter q =>
    obtain ⟨t, ht, out, ho, entered⟩ := desc q fs aux depth haux
    have hroom : S+1 ≤ boundedSpace S A d B w v e := le_max_left ..
    cases h : prog.describe q with
    | inl r =>
      rw [h] at entered
      have linked := entered.linkRoutine (routine a) (fun j ↦ Sum.inr ⟨Call.describe, j⟩)
        (some (.inl .described)) (fun _ ↦ rfl)
      have bit := described_step a (atControl w v (.returned r) fs out [true]) true rfl
      have pop := spaceRun_of_steps (cap := S+1) bit (fun k ↦ Nat.add_le_add_right (entered.final_cap k) 1)
      rw [clearSignal] at pop
      have run := (linked.mono_cap ((Nat.le_succ S).trans hroom)).trans (pop.mono_cap hroom)
      refine ⟨t+1, (Nat.add_le_add_right ht 1).trans (le_max_left ..), out, ho, ?_⟩
      simpa [Program.step, h, label, invoke, Actions.callee] using run
    | inr k =>
      rw [h] at entered
      have linked := entered.linkRoutine (routine a) (fun j ↦ Sum.inr ⟨Call.describe, j⟩)
        (some (.inl .described)) (fun _ ↦ rfl)
      have bit := described_step a (atControl w v (.scan q k 0) fs out [false]) false rfl
      have pop := spaceRun_of_steps (cap := S+1) bit (fun j ↦ Nat.add_le_add_right (entered.final_cap j) 1)
      rw [clearSignal] at pop
      have run := (linked.mono_cap ((Nat.le_succ S).trans hroom)).trans (pop.mono_cap hroom)
      refine ⟨t+1, (Nat.add_le_add_right ht 1).trans (le_max_left ..), out, ho, ?_⟩
      simpa [Program.step, h, label, invoke, Actions.callee] using run

/-- Simulate the full Schur recursion with an exponential-time, polynomial-space
descriptor while preserving both bounds across each linked action. -/
theorem eval_run_bounded (spec : Contracts a prog w v B lim ready pending Bd)
    (desc : DescribeBounded a prog w v Bd S d ready) (arity : prog.ArityLE lim)
    (ha : ∀ s, ready s → ∀ k, (s k).length ≤ A) {steps : ℕ} {start finish : Cfg n U Z c}
    (run : prog.Runs d steps start finish) (range : InRange lim start) (cursor : CursorRange prog start)
    (aux : Stacks K) (haux : ready aux) :
    ∃ t ≤ steps*boundedStepTime Bd B w v e, ∃ out, ready out ∧
      SpaceRun (routine a).standalone (boundedSpace S A d B w v e) t
        (some (label a start.1)) (atControl w v start.1 start.2 aux)
        (some (label a finish.1)) (atControl w v finish.1 finish.2 out) := by
  induction run generalizing aux with
  | done cfg depth =>
    refine ⟨0, by simp, aux, haux, .nil _ _ fun k ↦ ?_⟩
    exact (state_length cfg depth aux (ha aux haux) k).trans ((Nat.le_add_right ..).trans (le_max_right ..))
  | next depth _ ih =>
    obtain ⟨t, ht, mid, hm, step⟩ := step_bounded spec desc ha _ depth range cursor aux haux
    obtain ⟨u, hu, out, ho, rest⟩ := ih (inRange_step _ _ arity _ range) (cursorRange_step _ _ cursor) mid hm
    refine ⟨_, ?_, out, ho, step.trans rest⟩
    exact (Nat.add_le_add ht hu).trans_eq ((Nat.add_comm ..).trans (Nat.succ_mul ..).symm)

/-- The physical root call returns the requested coefficient with a cap independent
of the time spent inside scalar-entry queries. -/
theorem eval_root_bounded {entry : Entry n (Scalar c)}
    (spec : Contracts a (SchurKey.program (U := U) (Z := Z) entry) w v B (SchurKey.arityBound n U Z) ready pending Bd)
    (desc : DescribeBounded a (SchurKey.program (U := U) (Z := Z) entry) w v Bd S
      (Nat.clog 2 U+4+Nat.clog 2 n) ready)
    (ha : ∀ s, ready s → ∀ k, (s k).length ≤ A)
    (M : Matrix (Fin n) (Fin n) (Polynomial (Scalar c))) (he : ∀ i j z, entry i j z = (M i j).coeff z)
    (u : Limit U) (z : Limit Z) (aux : Stacks K) (haux : ready aux) :
    let depth := Nat.clog 2 U + 4 + Nat.clog 2 n
    ∃ t ≤ (5 + 6*SchurKey.arityBound n U Z)^(depth+1)*boundedStepTime Bd B w v e + 1, ∃ out, ready out ∧
      SpaceRun (routine a).standalone (boundedSpace S A depth B w v e) t (some (routine a).entry)
        (atControl (c := c) w v (.enter (SchurKey.root (n := n) u z)) [] aux) none
        (atControl w v (.returned ((M.charpolyRev.coeff u.val).coeff z.val)) ([] : List (F n U Z c)) out) := by
  let depth := Nat.clog 2 U+4+Nat.clog 2 n
  let finish : Cfg n U Z c := (.returned ((M.charpolyRev.coeff u.val).coeff z.val), [])
  obtain ⟨m, hm, run⟩ := SchurKey.run M entry he u z
  have startRange : InRange (SchurKey.arityBound n U Z) (c := c) (.enter (SchurKey.root (n := n) u z), []) := by
    simp [InRange]
  have startCursor : CursorRange (SchurKey.program entry) (.enter (SchurKey.root (n := n) u z), []) := by
    simp [CursorRange]
  obtain ⟨t,ht,out,ho,hr⟩ := eval_run_bounded spec desc (SchurKey.arity entry) ha run startRange startCursor aux haux
  have stop := return_to_caller a (atControl w v finish.1 finish.2 out) rfl
  have last : SpaceRun (routine a).standalone (runSpace A depth B w v e) 1
      (some (.inl .returned)) (atControl w v finish.1 finish.2 out) none (atControl w v finish.1 finish.2 out) :=
    spaceRun_of_steps stop fun k ↦ Nat.add_le_add
      (state_length (d := depth) finish (Nat.zero_le _) out (ha _ ho) k) (by dsimp [stepBudget]; omega)
  exact ⟨_, Nat.add_le_add_right (ht.trans (Nat.mul_le_mul_right _ hm)) _, out, ho,
    hr.trans (last.mono_cap (le_max_right ..))⟩

end RankQuery.Stack.Engine

end VPVNP
end Computability
end OAI

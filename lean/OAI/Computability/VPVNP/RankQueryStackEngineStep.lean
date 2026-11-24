import OAI.Computability.VPVNP.RankQueryStackEngineSpec

/-! # One abstract determinant transition in the linked bit-stack control -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Engine

open RAMTape Evaluator.InputBank

variable {n U Z p e : ℕ} {c : SliceArithmetic.Vector p e} {K : Type}
variable [DecidableEq K] [Fact p.Prime] [NeZero e]

private theorem setSignal (l h : Data) (f g r : List Bool) (s : Stacks K) :
    Function.update (store l h f r s) .condition g = store l h g r s := by
  funext k; cases k with
  | frame i => cases i <;> rfl
  | _ => rfl

private theorem setDirection (l h : Data) (f r : List Bool) (s : Stacks K) :
    Function.update (store l h f r s) (.frame (.inl 0)) [] = store (Function.update l 0 []) h f r s := by
  funext k
  cases k with
  | frame j => cases j with
    | inl i => by_cases hh : i = 0 <;> simp [store, Function.update, hh]
    | inr i => rfl
  | _ => rfl

omit [Fact p.Prime] [NeZero e] in
private theorem frameTag (w v : ℕ) (f : F n U Z c) (fs : List (F n U Z c)) :
    ∃ b tail, history w v (f :: fs) 0 = b :: tail := by
  cases f <;> exact ⟨true, _, rfl⟩

/-- Time bound for simulating an abstract evaluator transition with the installed actions and
ten encoded frame fields. -/
def stepBudget (B w v e : ℕ) : ℕ := 4*(B+10*(3*max 1 (max w (e*v))+2)+5)

variable {a : Actions K} {prog : Program (Key n U Z) (Scalar c)} {w v B lim Bd : ℕ}
variable {ready : Stacks K → Prop} {pending : Key n U Z → Stacks K → Prop}

omit [NeZero e] in
private theorem saveActivate (spec : Contracts a prog w v B lim ready pending Bd)
    (q : Key n U Z) (f : F n U Z c) (fs : List (F n U Z c)) (aux : Stacks K) (hp : pending q aux) :
    ∃ t ≤ 10*(3*max 1 (max w (e*v))+2)+1+B, ∃ out, ready out ∧
      StackRuns (routine a).standalone t (some (invoke a .save))
        (store (nativeFrame w v f) (history w v fs) [] [] aux) (some (invoke a .describe))
        (atControl w v (.enter q) (f :: fs) out) := by
  obtain ⟨ts, hs, save⟩ := save_runs a w v f fs [] aux
  obtain ⟨ta, ha, out, ho, active⟩ := spec.activate q (f :: fs) aux hp
  exact ⟨_, Nat.add_le_add hs ha, out, ho, (call_runs a .save save).trans (call_runs a .activate active)⟩

omit [Fact p.Prime] [NeZero e] in
private theorem restoreDirection (w v : ℕ) (f : F n U Z c) (fs : List (F n U Z c)) (r : Scalar c)
    (aux : Stacks K) :
    ∃ t ≤ 10*(3*max 1 (max w (e*v))+1)+4, StackRuns (routine a).standalone t (some (.inl .returned))
      (atControl w v (.returned r) (f :: fs) aux)
      (some (invoke a (match f with | .left .. => .right | .right .. => .multiplyAdd)))
      (store (popped w v f) (history w v fs) [] (scalar v r) aux) := by
  obtain ⟨b, tail, hh⟩ := frameTag w v f fs
  have start := return_to_frame a (atControl w v (.returned r) (f :: fs) aux) b tail hh
  obtain ⟨t, ht, hr⟩ := restore_runs a w v f fs (scalar v r) aux
  let s := store (nativeFrame w v f) (history w v fs) [] (scalar v r) aux
  cases f with
  | left q k a' =>
    have h := direction_step a s false rfl
    rw [show Function.update s (.frame (.inl 0)) [] = _ from setDirection ..] at h
    exact ⟨_, by omega, (start.trans (call_runs a .restore hr)).trans h⟩
  | right q k a' l =>
    have h := direction_step a s true rfl
    rw [show Function.update s (.frame (.inl 0)) [] = _ from setDirection ..] at h
    exact ⟨_, by omega, (start.trans (call_runs a .restore hr)).trans h⟩

/-- A transition of the typed Schur continuation machine uses a fixed number
of subroutine calls, including both frame operations when switching operands. -/
theorem step_runs_separate (spec : Contracts a prog w v B lim ready pending Bd) (cfg : Cfg n U Z c)
    (range : InRange lim cfg) (cursor : CursorRange prog cfg) (aux : Stacks K) (ha : ready aux) :
    ∃ t ≤ (match cfg.1 with | .enter _ => Bd+1 | _ => stepBudget B w v e), ∃ out, ready out ∧ StackRuns (routine a).standalone t
      (some (label a cfg.1)) (atControl w v cfg.1 cfg.2 aux) (some (label a (prog.step cfg).1))
      (atControl w v (prog.step cfg).1 (prog.step cfg).2 out) := by
  obtain ⟨ctl, fs⟩ := cfg
  cases ctl with
  | enter q =>
    obtain ⟨t, ht, out, ho, desc⟩ := spec.describe q fs aux ha
    cases h : prog.describe q with
    | inl r =>
      rw [h] at desc
      have hs := described_step a (atControl w v (.returned r) fs out [true]) true rfl
      unfold atControl at hs
      rw [setSignal] at hs
      have hr := (call_runs a .describe desc).trans hs
      refine ⟨t+1, Nat.add_le_add_right ht _, out, ho, ?_⟩
      simpa [Program.step, h, label, atControl] using hr
    | inr k =>
      rw [h] at desc
      have hs := described_step a (atControl w v (.scan q k 0) fs out [false]) false rfl
      unfold atControl at hs
      rw [setSignal] at hs
      have hr := (call_runs a .describe desc).trans hs
      refine ⟨t+1, Nat.add_le_add_right ht _, out, ho, ?_⟩
      simpa [Program.step, h, label, atControl] using hr
  | scan q k acc =>
    cases k with
    | zero =>
      obtain ⟨t, ht, out, ho, scan⟩ := spec.scanZero q acc fs aux ha
      have hs := scanned_step a (atControl w v (.returned acc) fs out [true]) true rfl
      unfold atControl at hs
      rw [setSignal] at hs
      exact ⟨_, by change _ ≤ stepBudget B w v e; unfold stepBudget; omega, out, ho, (call_runs a .scan scan).trans hs⟩
    | succ k =>
      obtain ⟨t, ht, next, hn, scan⟩ := spec.scanSucc q k acc fs aux range.1 cursor.1 ha
      let frame := Frame.left q k acc
      have hs := scanned_step a (store (nativeFrame w v frame) (history w v fs) [false] [] next) false rfl
      rw [setSignal] at hs
      obtain ⟨u, hu, out, ho, rest⟩ := saveActivate spec (prog.left q k) frame fs next hn
      exact ⟨_, by change _ ≤ stepBudget B w v e; unfold stepBudget; omega, out, ho, ((call_runs a .scan scan).trans hs).trans rest⟩
  | returned r =>
    cases fs with
    | nil => exact ⟨0, Nat.zero_le _, aux, ha, .nil ..⟩
    | cons f fs =>
      have hk := range.2 f List.mem_cons_self
      obtain ⟨s, hs, head⟩ := restoreDirection (a := a) w v f fs r aux
      cases f with
      | left q k acc =>
        obtain ⟨t, ht, next, hn, right⟩ := spec.right q k acc r fs aux hk (cursor.2 _ List.mem_cons_self) ha
        obtain ⟨u, hu, out, ho, tail⟩ := saveActivate spec (prog.right q k) (.right q k acc r) fs next hn
        exact ⟨_, by change _ ≤ stepBudget B w v e; unfold stepBudget; omega, out, ho, (head.trans (call_runs a .right right)).trans tail⟩
      | right q k acc l =>
        obtain ⟨t, ht, out, ho, mac⟩ := spec.multiplyAdd q k acc l r fs aux hk ha
        exact ⟨_, by change _ ≤ stepBudget B w v e; unfold stepBudget; omega, out, ho, head.trans (call_runs a .multiplyAdd mac)⟩

theorem step_runs (spec : Contracts a prog w v B lim ready pending) (cfg : Cfg n U Z c)
    (range : InRange lim cfg) (cursor : CursorRange prog cfg) (aux : Stacks K) (ha : ready aux) :
    ∃ t ≤ stepBudget B w v e, ∃ out, ready out ∧ StackRuns (routine a).standalone t
      (some (label a cfg.1)) (atControl w v cfg.1 cfg.2 aux) (some (label a (prog.step cfg).1))
      (atControl w v (prog.step cfg).1 (prog.step cfg).2 out) := by
  obtain ⟨t,ht,out,ho,run⟩ := step_runs_separate spec cfg range cursor aux ha
  refine ⟨t, ?_, out, ho, run⟩
  cases h : cfg.1 <;> rw [h] at ht <;> first | exact ht | change t ≤ B+1 at ht; unfold stepBudget; omega

end RankQuery.Stack.Engine

end VPVNP
end Computability
end OAI

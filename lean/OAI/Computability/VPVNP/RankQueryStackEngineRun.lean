import OAI.Computability.VPVNP.RankQueryStackEngineStep
import OAI.Computability.VPVNP.RankQueryStackBounds

/-! # Execution and space of the physical Schur continuation control -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Engine

open RAMTape UniversalCountStack

variable {n U Z p e : ℕ} {c : SliceArithmetic.Vector p e} {K : Type}

private theorem live_length (w v : ℕ) (ctl : Ctl n U Z c) (i : Fin 10) :
    (live w v ctl i).length ≤ max 1 (max w (e*v)) := by
  cases ctl with
  | returned r => simp [live]
  | enter q =>
    refine Fin.cases (by simp [live, fields]) (fun j => ?_) i
    refine Fin.addCases (motive := fun i => (Fin.append (fun x => digits w (q.words x)) ![[],[],[]] i).length ≤ _)
      (fun x : Fin 6 => ?_) (fun x : Fin 3 => ?_) j
    · simp
    · rw [Fin.append_right]; fin_cases x <;> simp
  | scan q k a =>
    refine Fin.cases (by simp [live, fields]) (fun j => ?_) i
    refine Fin.addCases (motive := fun i => (Fin.append (fun x => digits w (q.words x))
      ![digits w k,scalar v a,[]] i).length ≤ _) (fun x : Fin 6 => ?_) (fun x : Fin 3 => ?_) j
    · simp
    · rw [Fin.append_right]; fin_cases x <;> simp

/-- The call-stack cap counts the nested tagged field strings in each history.
One bounded transition accounts for the private working space between calls. -/
def runSpace (A d B w v e : ℕ) :=
  max A (max (max 1 (max w (e*v))) (d*(2*max 1 (max w (e*v))+1))) + stepBudget B w v e

theorem state_length {A d w v : ℕ} (cfg : Cfg n U Z c) (hd : cfg.2.length ≤ d)
    (aux : Stacks K) (ha : ∀ k, (aux k).length ≤ A) (k : Port K) :
    (atControl w v cfg.1 cfg.2 aux [] k).length ≤ max A (max (max 1 (max w (e*v))) (d*(2*max 1 (max w (e*v))+1))) := by
  cases k with
  | frame j =>
    cases j with
    | inl i => exact (live_length w v cfg.1 i).trans ((le_max_left ..).trans (le_max_right ..))
    | inr i =>
      exact ((history_length_le w v cfg.2 i).trans (Nat.mul_le_mul_right _ hd)).trans
        ((le_max_right ..).trans (le_max_right ..))
  | aux k => exact (ha k).trans (le_max_left ..)
  | condition => exact Nat.zero_le _
  | result => cases cfg.1 <;> simp [atControl, store, output]

variable [DecidableEq K] [Fact p.Prime] [NeZero e]
variable {a : Actions K} {prog : Program (Key n U Z) (Scalar c)} {w v B lim A d : ℕ}
variable {ready : Stacks K → Prop} {pending : Key n U Z → Stacks K → Prop}

/-- Transfer a capped abstract execution to the finite bit-stack program. -/
theorem eval_run (spec : Contracts a prog w v B lim ready pending) (arity : prog.ArityLE lim)
    (ha : ∀ s, ready s → ∀ k, (s k).length ≤ A) {steps : ℕ} {start finish : Cfg n U Z c}
    (run : prog.Runs d steps start finish) (range : InRange lim start) (cursor : CursorRange prog start)
    (aux : Stacks K) (haux : ready aux) :
    ∃ t ≤ steps*stepBudget B w v e, ∃ out, ready out ∧
      SpaceRun (routine a).standalone (runSpace A d B w v e) t
        (some (label a start.1)) (atControl w v start.1 start.2 aux)
        (some (label a finish.1)) (atControl w v finish.1 finish.2 out) := by
  induction run generalizing aux with
  | done cfg depth =>
    refine ⟨0, by simp, aux, haux, .nil _ _ fun k => ?_⟩
    exact (state_length cfg depth aux (ha aux haux) k).trans (Nat.le_add_right ..)
  | next depth _ ih =>
    obtain ⟨t, ht, mid, hm, step⟩ := step_runs spec _ range cursor aux haux
    obtain ⟨u, hu, out, ho, rest⟩ := ih (inRange_step _ _ arity _ range) (cursorRange_step _ _ cursor) mid hm
    have bounded := spaceRun_of_steps step (fun k => Nat.add_le_add (state_length _ depth aux (ha aux haux) k) ht)
    refine ⟨_, ?_, out, ho, bounded.trans rest⟩
    exact (Nat.add_le_add ht hu).trans_eq ((Nat.add_comm ..).trans (Nat.succ_mul ..).symm)

/-- Run the supplied matrix coefficient query from its root to a native scalar
on the output port. The entire physical return stack has been emptied. -/
theorem eval_root {entry : Entry n (Scalar c)}
    (spec : Contracts a (SchurKey.program (U := U) (Z := Z) entry) w v B (SchurKey.arityBound n U Z) ready pending)
    (ha : ∀ s, ready s → ∀ k, (s k).length ≤ A)
    (M : Matrix (Fin n) (Fin n) (Polynomial (Scalar c))) (he : ∀ i j z, entry i j z = (M i j).coeff z)
    (u : Limit U) (z : Limit Z) (aux : Stacks K) (haux : ready aux) :
    let depth := Nat.clog 2 U + 4 + Nat.clog 2 n
    ∃ t ≤ (5 + 6*SchurKey.arityBound n U Z)^(depth+1)*stepBudget B w v e + 1, ∃ out, ready out ∧
      SpaceRun (routine a).standalone (runSpace A depth B w v e) t (some (routine a).entry)
        (atControl (c := c) w v (.enter (SchurKey.root (n := n) u z)) [] aux) none
        (atControl w v (.returned ((M.charpolyRev.coeff u.val).coeff z.val)) ([] : List (F n U Z c)) out) := by
  let depth := Nat.clog 2 U + 4 + Nat.clog 2 n
  let value := (M.charpolyRev.coeff u.val).coeff z.val
  let finish : Cfg n U Z c := (.returned value, [])
  obtain ⟨m, hm, hrun⟩ := SchurKey.run M entry he u z
  have startRange : InRange (SchurKey.arityBound n U Z) (c := c) (.enter (SchurKey.root (n := n) u z), []) := by
    simp [InRange]
  have startCursor : CursorRange (SchurKey.program entry) (.enter (SchurKey.root (n := n) u z), []) := by
    simp [CursorRange]
  obtain ⟨t,ht,out,ho,hr⟩ := eval_run spec (SchurKey.arity entry) ha hrun startRange startCursor aux haux
  have stop := return_to_caller a (atControl w v finish.1 finish.2 out) rfl
  have last : SpaceRun (routine a).standalone (runSpace A depth B w v e) 1
      (some (.inl .returned)) (atControl w v finish.1 finish.2 out) none (atControl w v finish.1 finish.2 out) :=
    spaceRun_of_steps stop fun k => Nat.add_le_add
      (state_length (d := depth) finish (Nat.zero_le _) out (ha _ ho) k) (by dsimp [stepBudget]; omega)
  exact ⟨_, Nat.add_le_add_right (ht.trans (Nat.mul_le_mul_right _ hm)) _, out, ho, hr.trans last⟩

end RankQuery.Stack.Engine

end VPVNP
end Computability
end OAI

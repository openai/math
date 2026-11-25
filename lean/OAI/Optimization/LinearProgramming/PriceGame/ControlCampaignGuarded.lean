import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignDriver

/-! # Statewise score guards for a campaign with a bounded physical multiplier -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Driver

/-- The original unary dimension is unchanged at every outer and inner control step. -/
def DimensionAt (N : ℕ) : PC → Prop
  | .campaign c => c.dimension = N
  | .trial c _ => c.dimension = N

/-- Exactly the condition used when the inner stack returns a root score array. -/
def OuterSafe : PC → Prop
  | .campaign _ => True
  | .trial c s => ∀ o,
      Trial.stepPacket c.dimension c.range Moment.probes c.state.population.experts s = .halt o →
      ∀ i < c.state.population.weights.length, o.scores[i]?.getD 0 ≤ (2*c.dimension)^274

/-- A closed control trace together with a state predicate at every instruction executed. -/
inductive GuardedSteps (P : PC → Prop) : PC → List (PackedQuery × Bool) → ℕ → PC → Prop where
  | refl (s) : GuardedSteps P s [] 0 s
  | silent {s t u tr n} (hs : P s) (h : step s = .proceed t) (rest : GuardedSteps P t tr n u) :
      GuardedSteps P s tr (n+1) u
  | answer {s f t u tr n q} (b : Bool) (hs : P s) (h : step s = .ask q f t)
      (rest : GuardedSteps P (if b then t else f) tr n u) : GuardedSteps P s ((q,b)::tr) (n+1) u

theorem GuardedSteps.forget {s t tr n} {P : PC → Prop} (h : GuardedSteps P s tr n t) :
    Steps s tr n t := by
  induction h with
  | refl => exact .refl _
  | silent hs h _ ih => exact .silent h ih
  | answer b hs h _ ih => exact .answer b h ih

theorem GuardedSteps.mono {s t tr n} {P Q : PC → Prop} (h : GuardedSteps P s tr n t)
    (f : ∀ s, P s → Q s) : GuardedSteps Q s tr n t := by
  induction h with
  | refl => exact .refl _
  | silent hs h _ ih => exact .silent (f _ hs) h ih
  | answer b hs h _ ih => exact .answer b (f _ hs) h ih

theorem GuardedSteps.trans {P : PC → Prop} {p q r tr tr' n n'}
    (a : GuardedSteps P p tr n q) (b : GuardedSteps P q tr' n' r) :
    GuardedSteps P p (tr ++ tr') (n+n') r := by
  induction a with
  | refl => simpa using b
  | silent hs h _ ih => simpa [Nat.succ_add] using GuardedSteps.silent hs h (ih b)
  | answer bit hs h _ ih => simpa [Nat.succ_add] using GuardedSteps.answer bit hs h (ih b)

/-- Each stack instruction before its root return preserves the fixed outer dimension;
a non-halting trial instruction needs no score check. -/
theorem GuardedSteps.of_trial {N : ℕ} (c : CampaignCursor) (hc : c.dimension = N) {p q tr n}
    (h : Trial.Steps (kernel c) (2*Moment.probes) p tr n q) :
    GuardedSteps (fun v => OuterSafe v ∧ DimensionAt N v) (.trial c p) tr n (.trial c q) := by
  induction h with
  | refl => exact .refl _
  | @silent s t u tr n h _ ih =>
    refine .silent (s := .trial c s) (t := .trial c t) ⟨?_,hc⟩ ?_ ih
    · intro o z
      change Trial.step (kernel c) (2*Moment.probes) _ = .halt o at z
      rw [h] at z
      cases z
    · change (match Trial.step (kernel c) (2*Moment.probes) _ with
        | .proceed t => Action.proceed (.trial c t)
        | .ask q f t => .ask q (.trial c f) (.trial c t)
        | .halt out => .proceed (.campaign (finishRound c out))) = _
      rw [h]
  | @answer s f t u tr n q bit h _ ih =>
    refine .answer (s := .trial c s) (f := .trial c f) (t := .trial c t) bit ⟨?_,hc⟩ ?_ ?_
    · intro o z
      change Trial.step (kernel c) (2*Moment.probes) _ = .halt o at z
      rw [h] at z
      cases z
    · change (match Trial.step (kernel c) (2*Moment.probes) _ with
        | .proceed t => Action.proceed (.trial c t)
        | .ask q f t => .ask q (.trial c f) (.trial c t)
        | .halt out => .proceed (.campaign (finishRound c out))) = _
      rw [h]
    · cases bit <;> exact ih

theorem guarded_one_round {N : ℕ} {c : CampaignCursor} (hc : 0 < c.left)
    (dim : c.dimension = N) {tr : List (PackedQuery × Bool)} {out : PackedRound}
    (guard : ∀ i < c.state.population.weights.length, out.scores[i]?.getD 0 ≤ (2*c.dimension)^274)
    (eval : Trial.Evaluates (kernel c) (2*Moment.probes)
      (.node (States.Mass.depth c.dimension) (rootInput c)) tr out) :
    GuardedSteps (fun v => OuterSafe v ∧ DimensionAt N v) (.campaign c) tr
      (Trial.nodeTicks (2*Moment.probes) (States.Mass.depth c.dimension) + tr.length+2)
      (.campaign (finishRound c out)) := by
  obtain ⟨last,inside,done⟩ := eval.halts
  have start : step (.campaign c) = .proceed (.trial c
      (Trial.initial (States.Mass.depth c.dimension) (rootInput c))) := by
    simp [step,campaignBoundary,Nat.ne_of_gt hc]
  have finish : step (.trial c last) = .proceed (.campaign (finishRound c out)) := by
    change (match Trial.step (kernel c) (2*Moment.probes) last with
      | .proceed t => Action.proceed (.trial c t)
      | .ask q f t => .ask q (.trial c f) (.trial c t)
      | .halt round => .proceed (.campaign (finishRound c round))) = _
    rw [done]
  have finalGuard : OuterSafe (.trial c last) := by
    intro o z
    change Trial.step (kernel c) (2*Moment.probes) last = .halt o at z
    rw [done] at z
    cases z
    exact guard
  have tail : GuardedSteps (fun v => OuterSafe v ∧ DimensionAt N v) (.trial c last) [] 1
      (.campaign (finishRound c out)) := .silent ⟨finalGuard,dim⟩ finish (.refl _)
  have full := (GuardedSteps.of_trial c dim inside).trans tail
  simpa using GuardedSteps.silent (s := .campaign c) (P := fun v => OuterSafe v ∧ DimensionAt N v) ⟨trivial,dim⟩ start full

end Driver
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignGuarded
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialGuarded

/-! # One complete marked root trial within a suspended outer campaign -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Driver

theorem GuardedSteps.lift_trial {P : PC → Prop} (c : CampaignCursor) {s t tr ticks}
    (h : Trial.GuardedSteps (fun s => P (.trial c s))
      (kernel c) (2*Moment.probes) s tr ticks t) :
    GuardedSteps P (.trial c s) tr ticks (.trial c t) := by
  induction h with
  | refl => exact .refl _
  | @silent s t u tr n hs h _ ih =>
    refine .silent (s := .trial c s) (t := .trial c t) hs ?_ ih
    change (match Trial.step (kernel c) (2*Moment.probes) s with
      | .proceed t => Action.proceed (.trial c t)
      | .ask q f t => .ask q (.trial c f) (.trial c t)
      | .halt out => .proceed (.campaign (finishRound c out))) = _
    rw [h]
  | @answer s f t u tr n q b hs h _ ih =>
    refine .answer (s := .trial c s) (f := .trial c f) (t := .trial c t) b hs ?_ ?_
    · change (match Trial.step (kernel c) (2*Moment.probes) s with
        | .proceed t => Action.proceed (.trial c t)
        | .ask q f t => .ask q (.trial c f) (.trial c t)
        | .halt out => .proceed (.campaign (finishRound c out))) = _
      rw [h]
    · cases b <;> exact ih

/-- Enter a marked root trial and advance the suspended outer state using its actual
return. The inner path predicate includes the final inner instruction. -/
theorem guarded_round_of_marked_root {P : PC → Prop} {c : CampaignCursor} (left : 0 < c.left)
    (outer : P (.campaign c)) {tr out last}
    (path : Trial.GuardedSteps (fun s => P (.trial c s)) (kernel c) (2*Moment.probes)
      (Trial.initial (States.Mass.depth c.dimension) (rootInput c)) tr
      (Trial.nodeTicks (2*Moment.probes) (States.Mass.depth c.dimension)+tr.length) last)
    (stop : Trial.step (kernel c) (2*Moment.probes) last = .halt out) :
    GuardedSteps P (.campaign c) tr
      (Trial.nodeTicks (2*Moment.probes) (States.Mass.depth c.dimension)+tr.length+2)
      (.campaign (finishRound c out)) := by
  have enter : step (.campaign c) = .proceed (.trial c
      (Trial.initial (States.Mass.depth c.dimension) (rootInput c))) := by
    simp [step,campaignBoundary,Nat.ne_of_gt left]
  have finish : step (.trial c last) = .proceed (.campaign (finishRound c out)) := by
    change (match Trial.step (kernel c) (2*Moment.probes) last with
      | .proceed t => Action.proceed (.trial c t)
      | .ask q f t => .ask q (.trial c f) (.trial c t)
      | .halt round => .proceed (.campaign (finishRound c round))) = _
    rw [stop]
  have endStep : GuardedSteps P (.trial c last) [] 1 (.campaign (finishRound c out)) :=
    .silent path.stop finish (.refl _)
  simpa using GuardedSteps.silent outer enter ((GuardedSteps.lift_trial c path).trans endStep)

end Driver
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

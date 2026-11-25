import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignGuarded

/-! # Intersecting independently verified state predicates on the same execution -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Driver

/-- Determinism allows independent proofs of two predicates along the same public
transcript to be combined, keeping every executed instruction certified by both. -/
theorem GuardedSteps.zip {P Q : PC → Prop} {s t tr n}
    (a : GuardedSteps P s tr n t) (b : GuardedSteps Q s tr n t) :
    GuardedSteps (fun s => P s ∧ Q s) s tr n t := by
  induction a with
  | refl s => exact .refl _
  | @silent s t u tr n hp h _ ih =>
    cases b with
    | silent hq k rest =>
      have same := Action.proceed.inj (h.symm.trans k)
      cases same
      exact .silent ⟨hp,hq⟩ h (ih rest)
    | answer bit hq k rest => cases h.symm.trans k
  | @answer s f t u tr n q bit hp h _ ih =>
    cases b with
    | silent hq k rest => cases h.symm.trans k
    | answer _ hq k rest =>
      obtain ⟨_,reflF,reflT⟩ := Action.ask.inj (h.symm.trans k)
      cases reflF
      cases reflT
      exact .answer bit ⟨hp,hq⟩ h (ih rest)

/-- A state predicate including the terminal state. -/
structure GuardedRun (P : PC → Prop) (s : PC) (tr : List (PackedQuery × Bool)) (n : ℕ) (t : PC) : Prop where
  steps : GuardedSteps P s tr n t
  endpoint : P t

theorem GuardedRun.zip {P Q : PC → Prop} {s t tr n}
    (a : GuardedRun P s tr n t) (b : GuardedRun Q s tr n t) :
    GuardedRun (fun v => P v ∧ Q v) s tr n t :=
  ⟨a.steps.zip b.steps, a.endpoint, b.endpoint⟩

end Driver
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

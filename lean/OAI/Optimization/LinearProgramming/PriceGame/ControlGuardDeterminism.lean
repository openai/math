import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignGuarded

/-! Equality of full data-only endpoint states after the same public transcript and
the same number of silent and answered instructions. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Driver

theorem GuardedSteps.target_eq {P Q : PC → Prop} {s t u tr n}
    (a : GuardedSteps P s tr n t) (b : GuardedSteps Q s tr n u) : t = u := by
  induction a generalizing u with
  | refl s => cases b; rfl
  | @silent s t v tr n hp h _ ih =>
    cases b with
    | silent hq k rest =>
      have same := Action.proceed.inj (h.symm.trans k)
      cases same
      exact ih rest
    | answer bit hq k rest => cases h.symm.trans k
  | @answer s f t v tr n q bit hp h _ ih =>
    cases b with
    | silent hq k rest => cases h.symm.trans k
    | answer _ hq k rest =>
      obtain ⟨_,reflF,reflT⟩ := Action.ask.inj (h.symm.trans k)
      cases reflF
      cases reflT
      exact ih rest

end Driver
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

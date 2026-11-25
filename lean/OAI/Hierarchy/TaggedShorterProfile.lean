import OAI.Hierarchy.TaggedShorterChoice
import OAI.Hierarchy.TaggedWidthProfile

namespace OAI
/-! # A common shorter-call allocation across a smooth width profile -/

namespace Hierarchy.TaggedShorterBudget

/-- A single cofinal protocol meets all transport prices and the prescribed
weighted slot budget over the entire compact width range. -/
theorem choose {u : ℝ→ℝ} {r A ε : ℝ} (profile : TaggedWidthProfile.Admissible r u)
    (hε : 0<ε) {P : ℝ → ℝ → ℝ → ℝ → ℝ → Prop} (protocols : Cofinal P) :
    ∃ δ η ξ p q Q σ L : ℝ, P p q Q σ L ∧ Choice u A ε p q Q σ L δ η ξ :=
  choose_of_prices (profile.uniform_prices A) hε protocols

end Hierarchy.TaggedShorterBudget

end OAI

import OAI.Hierarchy.TaggedRadixPacking
import OAI.Hierarchy.TaggedWidePhysical

namespace OAI
/-! # Logarithmic-width tagged approximation from the cofinal routing readout -/
noncomputable section
namespace Hierarchy.Tagged
open Catalyst Filter

/-- The numerical cofinality statement together with its selected physical
routing readouts. A readout contains its dyadic allocation, chronological row
counts and pruned trivalent circuits for all socket replacements. -/
structure CofinalReadouts (F : Type*) [Field F] (k : ℕ) where
  parameters : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop
  protocols : ∀ A : ℝ,1<A → TaggedShorterBudget.Cofinal (parameters A)
  readout : ∀ {u : ℝ → ℝ} {κ A ε p q Q σ L δ η ξ : ℝ},
    TaggedWidthProfile.Admissible (profile F k 1) u → 0<κ → 1+κ≤A → 0<ε →
    parameters A p q Q σ L → TaggedShorterBudget.Choice u A (ε/2) p q Q σ L δ η ξ →
    Nonempty (ProtocolReadout F k u κ A δ ξ)

variable {F : Type*} [Field F] {k : ℕ}

theorem feasible_of_protocol_readout (hk : 0<k) (P : CofinalReadouts F k) {r : ℝ} (hr : 0<r) :
    Feasible F k 1 r :=
  feasible_at_one_of_reductions Radix.packing_bound
    (widthReductions_of_protocol hk P.protocols P.readout) hr

theorem cheap_of_protocol_readout (hk : 0<k) (P : CofinalReadouts F k) {r : ℝ} (hr : 0<r) :
    ∃ A C : ℝ, 0<A ∧ 0<C ∧ ∀ᶠ h : ℕ in atTop,
      ∃ X : Approximation F k (pins h h), (X.size:ℝ) ≤ A*work h h r ∧
        X.Gap (coeff F h h) (gap C h) ∧
        X.Gap (coeff F h h) ((2:ℝ)^h*(2:ℝ)^(-Real.sqrt h)) :=
  cheap_of_reductions Radix.packing_bound
    (widthReductions_of_protocol hk P.protocols P.readout) hr

end Hierarchy.Tagged

end
end OAI

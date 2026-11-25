import OAI.Hierarchy.TaggedAmplification
import OAI.Hierarchy.TaggedAmplificationScale
import OAI.Hierarchy.TaggedExactFeasible

namespace OAI
/-! # Amplification for bitonic tagged verifiers on all allowed batches -/

noncomputable section
namespace Hierarchy.Tagged

open Catalyst CorrectionFrame Filter

/-- The bitonic verifier pays for quadratic correction spacing. This polynomial
spacing suffices in the width induction, including all integer batch sizes in
the prescribed address-height range. -/
theorem amplified_batches (F : Type*) [Field F] :
    ∃ K : ℕ, ∀ b : ℝ, 0 < b → ∀ᶠ h : ℕ in atTop,
    ∀ {k w s : ℕ} (X : Approximation F k (pins h w)) {D : ℝ},
      0<s → Real.logb 2 s ≤ (h:ℝ)^b → X.Gap (coeff F h w) D →
      4*(k:ℝ)*(Real.logb 2 (((h+1)^2:ℕ):ℝ)+3) ≤ D →
      ∃ Y : Approximation F k (s*pins h w), Y.width = copiesWidth s X.width ∧
        Y.size ≤ K*s*X.size ∧ Y.Gap (dataProduct s (coeff F h w))
          ((s:ℝ)*D/(2*(((h+1)^2:ℕ):ℝ))) := by
  obtain ⟨K,make⟩ := amplify_exact F 16384
  refine ⟨K,fun b hb => ?_⟩
  filter_upwards [eventual_selector_budget b hb,eventually_ge_atTop (1:ℕ)] with h selector hh
  intro k w s X D hs l gap enough
  have lower : 2^h ≤ pins h w := by
    unfold pins
    have := Nat.mul_le_mul_left (2^h) hh
    omega
  have direct : pins h w ≤ X.size := by
    simp [Approximation.size,Fintype.card_sum]; omega
  exact make X (coeff F h w) (Exact.typedNetwork F h w) (Exact.typedNetwork_value F h w)
    (Exact.correction_budget F hh X) hs
    (by nlinarith only [hh, Nat.zero_le (h^2)]) ((selector s hs l).trans (lower.trans direct))
    enough gap


end Hierarchy.Tagged

end
end OAI

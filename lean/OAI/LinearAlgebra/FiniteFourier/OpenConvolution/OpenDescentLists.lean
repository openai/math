import OAI.LinearAlgebra.FiniteFourier.IntegralOpenDescent
import OAI.LinearAlgebra.FiniteFourier.OpenConvolutionCompile

/-! # Costs of the assembled localized convolution lists

The local reductions retain their child lengths after gluing.
Inserting optimal integral child programs therefore gives a bound by the
sum of the smaller integral convolution costs.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace OpenConvolution

open scoped BigOperators

variable {n : ℕ} {B₀ B₁ B₂ : Type*} [Fintype B₀] [Fintype B₁] [Fintype B₂]
    {a : B₀ → ℕ} {b : B₁ → ℕ} {c : B₂ → ℕ}

/-- Pointwise witness for integral open descent, with the child volume and
range required for the shorter-length cost recurrence. -/
theorem fromLocalizedLists (p₀ : OpenConvolution ℚ n B₀ a) (p₁ : OpenConvolution ℚ n B₁ b)
    (L : Finset ℕ) (h₀ : p₀.Localized (denominatorsAvoiding {2}))
    (h₁ : p₁.Localized (denominatorsAvoiding L)) {budget s : ℕ}
    (next : ∀ U : Finset ℕ, Disjoint U L → 2 ∉ U → (∀ p ∈ U, Nat.Prime p) →
      ∃ p₂ : OpenConvolution ℚ n B₂ c, p₂.Localized (denominatorsAvoiding U) ∧ p₂.linearCost ≤ budget)
    (hV₀ : ∑ i, a i ≤ 3*8*(9*n)) (hV₁ : ∑ i, b i ≤ 3*6*(9*n)) (hV₂ : ∑ i, c i ≤ 3*6*(9*n))
    (ha : ∀ i, 0 < a i ∧ a i ≤ s) (hb : ∀ i, 0 < b i ∧ b i ≤ s) (hc : ∀ i, 0 < c i ∧ c i ≤ s) :
    let len := Sum.elim a (Sum.elim b c)
    ∃ p : OpenConvolution ℤ n (B₀ ⊕ (B₁ ⊕ B₂)) len,
      (∀ i, 0 < len i ∧ len i ≤ s) ∧ (∑ i, len i) ≤ 540*n ∧ p.RealizesMultiple 1 ∧
      p.linearCost ≤ p₀.linearCost+p₁.linearCost+budget+2*(2*n-1) := by
  obtain ⟨p, he, hC⟩ := integralOpenDescent p₀ p₁ L h₀ h₁ next
  refine ⟨p, ?_, childLengthSum_le hV₀ hV₁ hV₂, he, hC⟩
  rintro (i | (i | i))
  · exact ha i
  · exact hb i
  · exact hc i

/-- Compile all the short gates in the three lists. The shared operand paths
are charged separately, as required by the arithmetic program model. -/
theorem cost_of_localizedLists (p₀ : OpenConvolution ℚ n B₀ a) (p₁ : OpenConvolution ℚ n B₁ b)
    (L : Finset ℕ) (h₀ : p₀.Localized (denominatorsAvoiding {2}))
    (h₁ : p₁.Localized (denominatorsAvoiding L)) {budget : ℕ}
    (next : ∀ U : Finset ℕ, Disjoint U L → 2 ∉ U → (∀ p ∈ U, Nat.Prime p) →
      ∃ p₂ : OpenConvolution ℚ n B₂ c, p₂.Localized (denominatorsAvoiding U) ∧ p₂.linearCost ≤ budget)
    (hV₀ : ∑ i, a i ≤ 3*8*(9*n)) (hV₁ : ∑ i, b i ≤ 3*6*(9*n)) (hV₂ : ∑ i, c i ≤ 3*6*(9*n)) :
    integralConvolutionCost n ≤
      3*(p₀.linearCost+p₁.linearCost+budget+2*(2*n-1)) + 2*(540*n) + (2*n-1) +
        ((∑ i, integralConvolutionCost (a i)) + (∑ i, integralConvolutionCost (b i)) +
          ∑ i, integralConvolutionCost (c i)) := by
  obtain ⟨p, he, hC⟩ := integralOpenDescent p₀ p₁ L h₀ h₁ next
  have htotal := p.integralConvolutionCost_le he
  have hsize := childLengthSum_le hV₀ hV₁ hV₂
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at htotal hsize
  omega

end OpenConvolution

end FiniteFourier
end LinearAlgebra
end OAI

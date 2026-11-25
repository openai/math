import OAI.LinearAlgebra.FiniteFourier.ConvolutionBezout
import OAI.LinearAlgebra.FiniteFourier.OpenConvolutionClear
import OAI.LinearAlgebra.FiniteFourier.DenominatorPrimes

/-! # Combining the three localized convolution lists

The quantitative inputs on the lists are separated from their assembly:
the latter retains every child length and applies both operand maps to
separate inputs. In the binary model two additional scalar combinations
suffice per final output.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped BigOperators

namespace OpenConvolution

variable {n : ℕ} {B₀ B₁ B₂ : Type*} {a : B₀ → ℕ} {b : B₁ → ℕ} {c : B₂ → ℕ}

/-- A rational formula for ordinary convolution whose prescribed constants
have denominators in the given multiplicative submonoid. -/
structure Localized {B : Type*} {s : B → ℕ} (p : OpenConvolution ℚ n B s)
    (S : Submonoid ℕ) : Prop where
  input : p.input.DenominatorsIn S
  output : p.output.DenominatorsIn S
  correct : p.RealizesMultiple 1

/-- Combine the localized reductions over the integers with no change to the
length or multiplicity of their child convolution gates. -/
theorem integralOpenDescentOfScales
    (p₀ : OpenConvolution ℚ n B₀ a) (p₁ : OpenConvolution ℚ n B₁ b)
    (p₂ : OpenConvolution ℚ n B₂ c) {S₀ S₁ S₂ : Submonoid ℕ}
    (h₀ : p₀.Localized S₀) (h₁ : p₁.Localized S₁) (h₂ : p₂.Localized S₂)
    (hodd : ∀ D ∈ S₀, Odd D)
    (hgcd : ∀ d₁ ∈ S₁, 0 < d₁ → ∀ d₂ ∈ S₂, 0 < d₂ → ∃ k, d₁.gcd d₂ = 2^k) :
    ∃ p : OpenConvolution ℤ n (B₀ ⊕ (B₁ ⊕ B₂)) (Sum.elim a (Sum.elim b c)),
      p.RealizesMultiple 1 ∧
      p.linearCost ≤ p₀.linearCost + p₁.linearCost + p₂.linearCost + 2*(2*n-1) := by
  obtain ⟨q₀, D₀, _, hd₀, hI₀, hO₀, hq₀⟩ := p₀.clearDenominators S₀ h₀.input h₀.output h₀.correct
  obtain ⟨q₁, D₁, hp₁, hd₁, hI₁, hO₁, hq₁⟩ := p₁.clearDenominators S₁ h₁.input h₁.output h₁.correct
  obtain ⟨q₂, D₂, hp₂, hd₂, hI₂, hO₂, hq₂⟩ := p₂.clearDenominators S₂ h₂.input h₂.output h₂.correct
  obtain ⟨k, hk⟩ := hgcd _ hd₁ hp₁ _ hd₂ hp₂
  obtain ⟨p, he, hsize⟩ := threeListBezout q₀ q₁ q₂ hq₀ hq₁ hq₂ (hodd _ hd₀) hk
  exact ⟨p, he, by simpa only [linearCost, hI₀, hI₁, hI₂, hO₀, hO₁, hO₂] using hsize⟩

/-- Choose the second dyadic circuit after observing the odd denominator primes
actually used by the first. The output is a single integral reduction for the
unscaled convolution with both maps explicitly costed. -/
theorem integralOpenDescent
    (p₀ : OpenConvolution ℚ n B₀ a) (p₁ : OpenConvolution ℚ n B₁ b)
    (L : Finset ℕ) (h₀ : p₀.Localized (denominatorsAvoiding {2}))
    (h₁ : p₁.Localized (denominatorsAvoiding L)) {budget : ℕ}
    (next : ∀ U : Finset ℕ, Disjoint U L → 2 ∉ U → (∀ p ∈ U, Nat.Prime p) →
      ∃ p₂ : OpenConvolution ℚ n B₂ c, p₂.Localized (denominatorsAvoiding U) ∧ p₂.linearCost ≤ budget) :
    ∃ p : OpenConvolution ℤ n (B₀ ⊕ (B₁ ⊕ B₂)) (Sum.elim a (Sum.elim b c)),
      p.RealizesMultiple 1 ∧
      p.linearCost ≤ p₀.linearCost + p₁.linearCost + budget + 2*(2*n-1) := by
  obtain ⟨q₀, D₀, _, hd₀, hI₀, hO₀, hq₀⟩ :=
    p₀.clearDenominators _ h₀.input h₀.output h₀.correct
  obtain ⟨q₁, D₁, hp₁, hd₁, hI₁, hO₁, hq₁⟩ :=
    p₁.clearDenominators _ h₁.input h₁.output h₁.correct
  obtain ⟨p₂, h₂, hcost⟩ := next (D₁.primeFactors.erase 2)
    (disjoint_oddFactors_of_mem_denominatorsAvoiding hd₁) (Finset.notMem_erase _ _)
    (fun p hp => (Nat.mem_primeFactors.mp (Finset.mem_of_mem_erase hp)).1)
  obtain ⟨q₂, D₂, _, hd₂, hI₂, hO₂, hq₂⟩ :=
    p₂.clearDenominators _ h₂.input h₂.output h₂.correct
  obtain ⟨k, hk⟩ := gcd_eq_pow_two_of_avoids_oddFactors hp₁ hd₂
  obtain ⟨p, he, hsize⟩ := threeListBezout q₀ q₁ q₂ hq₀ hq₁ hq₂ (odd_of_mem_denominatorsAvoiding_two hd₀) hk
  refine ⟨p, he, ?_⟩
  simp only [linearCost, hI₀, hI₁, hI₂, hO₀, hO₁, hO₂] at hsize hcost ⊢
  omega

/-- The child length sum from the three split jet lists in Theorem 9.3. -/
theorem childLengthSum_le [Fintype B₀] [Fintype B₁] [Fintype B₂]
    (h₀ : ∑ i, a i ≤ 3 * 8 * (9*n)) (h₁ : ∑ i, b i ≤ 3 * 6 * (9*n))
    (h₂ : ∑ i, c i ≤ 3 * 6 * (9*n)) :
    ∑ i, Sum.elim a (Sum.elim b c) i ≤ 540*n := by
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  omega

/-- Any common child-length upper bound passes to the assembled list. -/
theorem childLengthBound {s : ℕ} (ha : ∀ i, a i ≤ s) (hb : ∀ i, b i ≤ s)
    (hc : ∀ i, c i ≤ s) (i : B₀ ⊕ (B₁ ⊕ B₂)) : Sum.elim a (Sum.elim b c) i ≤ s := by
  rcases i with i | (i | i)
  · exact ha i
  · exact hb i
  · exact hc i

end OpenConvolution

end FiniteFourier
end LinearAlgebra
end OAI

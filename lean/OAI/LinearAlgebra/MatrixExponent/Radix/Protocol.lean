import OAI.LinearAlgebra.MatrixExponent.Radix.WideTag

/-! # Cost of installing the smaller tagged-permutation calls -/

namespace OAI.LinearAlgebra.MatrixExponent.Radix

/-- One layer of the routing protocol, restricted to payloads of length
`h^A`. The inductive cost is that of `L` copies of a shorter verifier.
The constant on the total payload stays bounded as the height ratio shrinks. -/
def Protocol (F : Type) [Field F] : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∃ Y : ℝ, 0 < Y ∧ ∃ J : ℕ,
    ∀ A : ℕ, J ≤ A → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ h : ℕ in Filter.atTop,
      ∃ l v M L : ℕ, 1 ≤ l ∧ (l : ℝ) ≤ τ * h ∧ Y * (h : ℝ) ^ A ≤ v ∧
        (L : ℝ) * (2 : ℝ) ^ l * v ≤ C * (2 : ℝ) ^ h * (h : ℝ) ^ A ∧
        (M : ℝ) ≤ (2 : ℝ) ^ h * (h : ℝ) ^ A * (h : ℝ) ^ ζ ∧
        ∀ s, Tag F l v s → ∃ m ≤ M + L * s, Tag F h (h ^ A) m

end OAI.LinearAlgebra.MatrixExponent.Radix

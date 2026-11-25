import OAI.LinearAlgebra.MatrixExponent.Tagged.Tags

/-! # Power-of-logarithm lower bound for verifying one permutation -/

namespace OAI.LinearAlgebra.MatrixExponent.Tagged
open Filter

/-- Only square payloads at powers of two are required. Count vertices
of exact trivalent networks. Any constant in the lower bound can be
absorbed by decreasing the positive exponent. -/
def Hard (F : Type) [Field F] : Prop :=
  ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ w : ℕ in atTop, ∀ m,
    Net F (inputs w (word w)) .unit (tag F w (word w)) m →
    (2 : ℝ) ^ w * w * (w : ℝ) ^ σ ≤ m

end OAI.LinearAlgebra.MatrixExponent.Tagged

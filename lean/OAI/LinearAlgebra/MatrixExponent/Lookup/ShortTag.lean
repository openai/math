import OAI.LinearAlgebra.MatrixExponent.Tagged.Tags

namespace OAI.LinearAlgebra.MatrixExponent.Lookup

/-- The ordinary-width tagged permutation estimate. -/
def ShortTag (F : Type) [Field F] (p : ℝ) : Prop :=
  ∃ C : ℝ, ∀ w : ℕ, 1 ≤ w → ∃ v : ℕ,
    Net F (Tagged.inputs w (word w)) .unit (Tagged.tag F w (word w)) v ∧
    (v : ℝ) ≤ C * (2 : ℝ) ^ w * (w : ℝ) ^ p

end OAI.LinearAlgebra.MatrixExponent.Lookup

import OAI.LinearAlgebra.MatrixExponent.Lookup.ShortTag

namespace OAI.LinearAlgebra.MatrixExponent.Radix

def Tag (F : Type) [Field F] (w v m : ℕ) : Prop :=
  Net F (Tagged.inputs w (word v)) .unit (Tagged.tag F w (word v)) m

/-- The wide-record estimate in the conditional stable sorting theorem. -/
def WideTag (F : Type) [Field F] : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ A : ℕ, 2 ≤ A ∧ ∃ C : ℝ, ∀ w v : ℕ, 1 ≤ w → w ^ A ≤ v →
    ∃ m : ℕ, Tag F w v m ∧ (m : ℝ) ≤ C * (2 : ℝ) ^ w * v * (w : ℝ) ^ ζ

end OAI.LinearAlgebra.MatrixExponent.Radix

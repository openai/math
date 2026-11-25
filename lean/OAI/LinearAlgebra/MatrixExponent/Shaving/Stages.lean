import OAI.LinearAlgebra.MatrixExponent.Shaving.FieldStage
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Uniform compression stages with a prescribed label-length bound -/

namespace OAI.LinearAlgebra.MatrixExponent.Shaving
open Filter

/-- The dictionary may name this many tables on the way into a stage.
As in Section 5, the logarithm in the label length is binary. -/
noncomputable def labelLimit (C : ℝ) (r n : ℕ) :=
  2^⌈C * (1 + Real.logb 2 (Nat.clog 2 n)) ^ r⌉₊

/-- The savings scale and extension-degree bound are fixed before
the input label length. The output uses the exponent-two bound. -/
def Macro (F : Type) [Field F] : Prop :=
  ∀ δ β : ℝ, 0 < δ → δ ≤ 1 / 10 → 0 < β → β ≤ 1 / 2 →
    ∃ α D : ℝ, 0 < α ∧ 0 < D ∧ ∀ a b ξ C : ℝ, ∀ r : ℕ,
      0 < a → a < α → β ≤ b → b ≤ 1 / 2 → 0 < ξ → 0 ≤ C →
      ∀ᶠ n : ℕ in atTop, ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : Module.Finite F K),
        (Module.finrank F K : ℝ) ≤ D * Real.log (Nat.clog 2 n) ∧
        ArityStep K n (labelLimit C r n) (dictionary n) b δ a ξ

end OAI.LinearAlgebra.MatrixExponent.Shaving

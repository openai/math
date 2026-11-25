import OAI.LinearAlgebra.MatrixExponent.Tagged.Hard
import OAI.LinearAlgebra.MatrixExponent.Shaving.Defs

/-! # The two size estimates in the tagged-permutation argument -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal
open Filter

/-- At every large scale and every fixed linear cost, some cheaply
realizable tensor resists simultaneous implementation for all small
powers. The permitted high-arity tables are specified by `L`. -/
def Resists (F : Type) [Field F] (L : Set (Table F)) : Prop :=
  ∀ C : ℕ, 4 ≤ C → ∃ k : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ w : ℕ in atTop,
    let N : ℕ := 2 ^ w
    ∃ (a : Wire) (U : Val a → Val .unit → F) (v : ℕ),
      wd a ≤ N ∧ Net F a .unit U v ∧ v ≤ N * w ^ k ∧
      ∀ d D m : ℕ, 1 ≤ d → (d : ℝ) ≤ (N : ℝ) ^ δ → D ^ 2 ≤ N →
        Wide F D L (copies a d) (copies .unit d) (power U d) m → C * N * d < m

/-- A uniform descent step along the exceptional lengths. The first
version pays a small power of the logarithm in exterior cost. The
second version allows special tables and pays constant exterior cost. -/
def Descent (F : Type) [Field F] (L : Set (Table F)) : Prop :=
  ¬Tagged.Hard F → ∃ C : ℕ, 4 ≤ C ∧ ∃ α : ℝ, 0 < α ∧ ∀ κ : ℝ, 0 < κ →
    ∃ᶠ w : ℕ in atTop,
      let N : ℕ := 2 ^ w
      ∀ (a b : Wire) (U : Val a → Val b → F) (v M : ℕ),
        Net F a b U v → v + wd a + wd b ≤ M → N ≤ M →
        (M : ℝ) ≤ (N : ℝ) ^ (21 / 20 : ℝ) →
        (∃ d m : ℕ, 1 ≤ d ∧ (d : ℝ) ≤ (N : ℝ) ^ κ ∧ PowerSize U d m ∧
          (m : ℝ) ≤ d * ((M : ℝ) * (w : ℝ) ^ (-α) + (wd a + wd b : ℕ) * (w : ℝ) ^ (α / 4))) ∧
        (∃ d D m : ℕ, 1 ≤ d ∧ (d : ℝ) ≤ (N : ℝ) ^ κ ∧ D ^ 2 ≤ N ∧
          Wide F D L (copies a d) (copies b d) (power U d) m ∧
          (m : ℝ) ≤ C * d * ((M : ℝ) * (w : ℝ) ^ (-α) + (wd a + wd b : ℕ)))

end OAI.LinearAlgebra.MatrixExponent.Diagonal

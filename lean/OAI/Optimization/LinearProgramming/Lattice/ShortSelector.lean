import OAI.Optimization.LinearProgramming.Lattice.LLLNative
import OAI.Optimization.LinearProgramming.Lattice.ShortSelectorCore

/-! The executable LLL-backed simultaneous approximation selector used by sign rounding. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

/-- Reduce the explicit rational graph lattice and read the approximation from the first row. -/
def lllShortSelector {p : ℕ} (M : ℕ) (u : Fin p → ℚ) : ℕ × (Fin p → ℤ) :=
  shortSelectorWith reduceRational M u

/-- Correctness of the native LLL backend for every rational input, in the precise form needed
by `roundingProgramWith_correct`. -/
theorem lllShortSelector_correct {p M : ℕ} (hp : 0 < p) (hM : 0 < M) (u : Fin p → ℚ) :
    0 < (lllShortSelector M u).1 ∧ (lllShortSelector M u).1 ≤ searchDenominator p M ^ (p+1) ∧
      ∀ i, |((lllShortSelector M u).1 : ℚ) * u i - (lllShortSelector M u).2 i| ≤
        1 / (8 * (p : ℚ) * M) :=
  shortSelectorWith_correct hp hM reduceRational reduceRational_spec u

end Lattice
end LinearProgramming
end Optimization
end OAI

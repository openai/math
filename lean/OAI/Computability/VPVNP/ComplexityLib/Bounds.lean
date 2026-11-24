import OAI.Computability.VPVNP.PolynomialBounds
import Cslib.Foundations.Data.Nat.PolynomialBound

/-! # Polynomial bounds in the two arithmetic circuit models -/

namespace OAI
namespace Computability
namespace VPVNP

namespace ComplexityLib

/-- The two polynomial growth conditions agree, including at indices below the
eventual threshold, whose values can be absorbed into a global leading constant. -/
theorem polynomiallyBounded_iff (f : ℕ → ℕ) :
    VPVNP.PolynomiallyBounded f ↔ Cslib.PolynomiallyBounded f := by
  rw [Cslib.polynomiallyBounded_iff_le]
  constructor
  · exact VPVNP.PolynomiallyBounded.exists_global_bound
  · rintro ⟨c, d, h⟩
    exact ((PolynomiallyBounded.const c).mul (PolynomiallyBounded.succ.pow d)).of_le h

end ComplexityLib

end VPVNP
end Computability
end OAI

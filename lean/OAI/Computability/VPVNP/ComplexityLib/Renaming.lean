import OAI.Computability.VPVNP.CircuitSize
import Mathlib.Algebra.MvPolynomial.Rename

/-! # Circuit size under variable renaming -/

namespace OAI
namespace Computability
namespace VPVNP

namespace ComplexityLib

variable {K X Y : Type*} [CommRing K]

/-- Renaming variables is a projection and cannot increase the number of binary gates. -/
private theorem circuitSize_rename_le (f : X → Y) (p : MvPolynomial X K) :
    circuitSize (MvPolynomial.rename f p) ≤ circuitSize p := by
  rw [MvPolynomial.rename_eq_aeval]
  exact circuitSize_projection_le (fun i => Sum.inl (f i)) p

/-- Relabelling the variables by a bijection preserves the minimum number of binary gates. -/
theorem circuitSize_renameEquiv (e : X ≃ Y) (p : MvPolynomial X K) :
    circuitSize (MvPolynomial.rename e p) = circuitSize p := by
  apply le_antisymm (circuitSize_rename_le e p)
  simpa only [MvPolynomial.rename_rename, e.symm_comp_self, MvPolynomial.rename_id_apply] using
    circuitSize_rename_le e.symm (MvPolynomial.rename e p)

end ComplexityLib

end VPVNP
end Computability
end OAI

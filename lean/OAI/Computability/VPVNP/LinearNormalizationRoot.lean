import OAI.Computability.VPVNP.LinearNormalizationLine
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Integrality from a polynomial restricted to a line

A direction where the top homogeneous part is nonzero makes the leading
coefficient of the line polynomial a unit. Rescaling this relation gives
a monic equation for every root in an extension algebra.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LinearNormalization

variable {K B A I : Type*} [Field K] [CommRing B] [Nontrivial B] [Algebra K B]
    [CommRing A] [Algebra B A]

theorem isIntegral_of_line_root (p : MvPolynomial I K) (h : I → B) (v : I → K) (x : A)
    (ht : MvPolynomial.eval v (MvPolynomial.homogeneousComponent p.totalDegree p) ≠ 0)
    (hx : Polynomial.aeval x (line p h v) = 0) : IsIntegral B x := by
  have htop : IsUnit ((line p h v).coeff p.totalDegree) := by
    rw [coeff_line_totalDegree]
    exact ht.isUnit.map (algebraMap K B)
  have hdegree := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_line_le p h v) htop.ne_zero
  have hu : IsUnit (line p h v).leadingCoeff := by simpa [Polynomial.leadingCoeff, hdegree] using htop
  refine ⟨hu.unit⁻¹.val • line p h v, Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hu, ?_⟩
  change Polynomial.aeval x (hu.unit⁻¹.val • line p h v) = 0
  rw [map_smul, hx, smul_zero]

end LinearNormalization

end VPVNP
end Computability
end OAI

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Choosing a direction for linear Noether normalization

Over an infinite field the highest homogeneous part of a nonzero polynomial
has a nonzero value on some vector whose first coordinate is nonzero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LinearNormalization

open MvPolynomial

/-- A monomial of maximal degree survives in the top homogeneous component. -/
theorem topComponent_ne_zero {σ R : Type*} [CommSemiring R] {p : MvPolynomial σ R}
    (hp : p ≠ 0) : homogeneousComponent p.totalDegree p ≠ 0 := by
  classical
  obtain ⟨d, hd, hdeg⟩ :=
    p.support.exists_mem_eq_sup (support_nonempty.mpr hp) (fun d => d.degree)
  change p.totalDegree = d.degree at hdeg
  intro h
  apply mem_support_iff.mp hd
  simpa [coeff_homogeneousComponent, hdeg.symm] using
    congrArg (fun q : MvPolynomial σ R => q.coeff d) h

/-- Choose a direction avoiding both the coordinate hyperplane and the zero set
of the highest homogeneous part. -/
theorem exists_direction {K : Type*} [Field K] [Infinite K] {n : ℕ}
    {p : MvPolynomial (Fin (n + 1)) K} (hp : p ≠ 0) :
    ∃ v : Fin (n + 1) → K, v 0 ≠ 0 ∧ eval v (homogeneousComponent p.totalDegree p) ≠ 0 := by
  classical
  by_contra! h
  apply mul_ne_zero (X_ne_zero (R := K) (0 : Fin (n + 1))) (topComponent_ne_zero hp)
  apply MvPolynomial.funext
  intro v
  by_cases hv : v 0 = 0
  · simp [hv]
  · simp [h v hv]

end LinearNormalization

end VPVNP
end Computability
end OAI

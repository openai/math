import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# A bounded monic relation for the certificate graph

In the effective Nullstellensatz argument used for Section 8.2, a generic
linear normalization makes the distinguished coordinate integral over an
embedded polynomial ring. A bounded nonzero relation in all the normalized
coordinates is available by counting monomials. The minimal polynomial
divides that relation over the polynomial ring, so replacing it by a monic
relation does not increase its multivariate total degree.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate

open MvPolynomial

private theorem eval_split {E S : Type*} [Field E] [CommRing S] [Algebra E S] {m : ℕ}
    (Q : Fin m → S) (T : S) (W : MvPolynomial (Fin (m + 1)) E) :
    Polynomial.eval₂ (aeval Q).toRingHom T (finSuccEquiv E m W) = aeval (Fin.cons T Q) W := by
  have he : (Polynomial.eval₂RingHom (aeval Q).toRingHom T).comp (finSuccEquiv E m).toRingHom =
      (aeval (Fin.cons T Q)).toRingHom := by
    apply ringHom_ext
    · intro c
      simp [finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [finSuccEquiv_X_zero]
      · simp [finSuccEquiv_X_succ]
  exact DFunLike.congr_fun he W

/-- If `Q` are algebraically independent and `T` is integral over their image
algebra, every nonzero relation in `(T,Q)` has a monic divisor which is itself a
relation. The divisor has no larger total degree, including in positive characteristic. -/
theorem monic_relation_of_relation {E S : Type*} [Field E] [CommRing S] [IsDomain S]
    [Algebra E S] {m : ℕ} (Q : Fin m → S) (T : S)
    (hinj : Function.Injective (aeval Q : MvPolynomial (Fin m) E →ₐ[E] S))
    (hint : IsIntegral (aeval Q : MvPolynomial (Fin m) E →ₐ[E] S).range T)
    (W : MvPolynomial (Fin (m + 1)) E) (hW : W ≠ 0) (hzero : aeval (Fin.cons T Q) W = 0) :
    ∃ U : MvPolynomial (Fin (m + 1)) E, (finSuccEquiv E m U).Monic ∧
      aeval (Fin.cons T Q) U = 0 ∧ U ∣ W ∧ U.totalDegree ≤ W.totalDegree := by
  let B := MvPolynomial (Fin m) E
  let φ : B →ₐ[E] S := aeval Q
  let : Algebra B S := φ.toRingHom.toAlgebra
  let : Module.IsTorsionFree B S := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  let e := AlgEquiv.ofInjective φ hinj
  have hInt : IsIntegral B T := (e.toRingEquiv.isIntegral_iff (by rfl) T).mpr hint
  let P := minpoly B T
  let split := finSuccEquiv E m
  have hroot : Polynomial.aeval T (split W) = 0 := (eval_split Q T W).trans hzero
  have hdiv : P ∣ split W := minpoly.isIntegrallyClosed_dvd hInt hroot
  have hmon : P.Monic := minpoly.monic hInt
  have hdvd : split.symm P ∣ W := by simpa using (map_dvd split.symm hdiv)
  refine ⟨split.symm P, ?_, ?_, hdvd, totalDegree_le_of_dvd_of_isDomain hdvd hW⟩
  · change (split (split.symm P)).Monic
    simpa using hmon
  · rw [← eval_split]
    change Polynomial.aeval T (split (split.symm P)) = 0
    rw [split.apply_symm_apply]
    exact minpoly.aeval B T

end RadicalCertificate

end VPVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.BranchCurveDimension
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Dimension at the retained point of a deformation

The local dimension at any closed point of an integral affine variety over
a field equals the dimension of the whole variety. This promotes the local
horizontal component in Proposition 9.2 to an affine curve.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

/-- Every closed point of affine space in dimension `n` has height `n`. -/
theorem affineSpace_point_height {K : Type*} [Field K] (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) K)) [m.IsMaximal] : m.height = n := by
  induction n with
  | zero =>
    have h := Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top' (I := m))
    simpa using h
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv K n).toRingEquiv
    let Q := m.map e
    have : Q.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let p := Q.under (MvPolynomial (Fin n) K)
    have : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing Q
    have hm : Q.height = m.height := e.height_map m
    rw [← hm, Polynomial.height_eq_height_add_one p Q, ih p, Nat.cast_succ]

/-- An integral Noether normalization gives both the dimension and the
height of each closed point of the affine domain. -/
theorem dimension_of_normalization {K A : Type*} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal]
    (n : ℕ) (g : MvPolynomial (Fin n) K →ₐ[K] A)
    (hinj : Function.Injective g) (hint : g.toRingHom.IsIntegral) :
    (m.height : WithBot ℕ∞) = ringKrullDim A ∧ ringKrullDim A = n := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let R := MvPolynomial (Fin n) K
  let : Algebra R A := g.toRingHom.toAlgebra
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Algebra.IsIntegral R A := ⟨hint⟩
  have : IsIntegrallyClosed R := inferInstanceAs (IsIntegrallyClosed (MvPolynomial (Fin n) K))
  let p := m.under R
  have : p.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal m
  have hheight : (n : ℕ∞) ≤ m.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p m, affineSpace_point_height n p]
    exact le_self_add
  have hdim : ringKrullDim A ≤ ringKrullDim R := by
    apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A))
    intro P Q hPQ
    exact Ideal.IsIntegral.under_lt_under (R := R) (I := P.asIdeal) (J := Q.asIdeal) hPQ
  have hR : ringKrullDim R = n := by simp [R]
  rw [hR] at hdim
  have low : (n : WithBot ℕ∞) ≤ m.height := by exact_mod_cast hheight
  have high : (m.height : WithBot ℕ∞) ≤ ringKrullDim A :=
    Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  exact ⟨le_antisymm high (hdim.trans low), le_antisymm hdim (low.trans high)⟩

/-- Closed points of an affine domain all have the full Krull dimension.
Noether normalization gives a finite polynomial subring; going down lifts
the full chain at the contracted closed point. -/
theorem affineDomain_point_height {K A : Type*} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨n, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  exact (dimension_of_normalization m n g hinj hint).1

/-- A finite isolated special fiber and the expected local dimension give an
affine curve through the retained point, with a dominant parameter. -/
theorem exists_affine_curve {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] (eqns : Finset A) (t : A) (m : Ideal A) [m.IsMaximal]
    (isolated : m ∈ (Ideal.span (eqns : Set A) ⊔ Ideal.span {t}).minimalPrimes)
    (dimension : (eqns.card : ℕ∞) < m.height) :
    ∃ P ∈ (Ideal.span (eqns : Set A)).minimalPrimes, P < m ∧ ringKrullDim (A ⧸ P) = 1 ∧
      Function.Injective (Polynomial.aeval (R := K) (Ideal.Quotient.mk P t)) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  obtain ⟨P, hP, hPm, htP, hheight⟩ := exists_horizontal_component eqns t m isolated dimension
  have : P.IsPrime := hP.isPrime
  let pt := m.map (Ideal.Quotient.mk P)
  have : pt.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (by simpa using hPm.le)
  refine ⟨P, hP, hPm, ?_, parameter_dominant _ (mt Ideal.Quotient.eq_zero_iff_mem.mp htP)
    pt Ideal.IsPrime.ne_top' ?_⟩
  · rw [← affineDomain_point_height (K := K) pt]
    change (m.map (Ideal.Quotient.mk P)).height = (1 : WithBot ℕ∞)
    rw [hheight, WithBot.coe_one]
  · apply Ideal.mem_map_of_mem
    have le : Ideal.span ({t} : Set A) ≤ m := le_sup_right.trans isolated.le
    exact le (Ideal.subset_span (Set.mem_singleton t))

end Branch

end BorderVNP
end Computability
end OAI

import OAI.LinearAlgebra.FiniteFourier.ProtectedRationals
import OAI.LinearAlgebra.FiniteFourier.SemilocalPivot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-! # Cyclotomic evaluation nodes over the two-local coefficient ring

The cyclotomic polynomial is imposed as a monic relation over a base which can already
contain roots of unity. Primitivity is checked in residue fields. Consequently distinct
nodes of each Fourier transform have unit differences, including after adjoining the jet
parameter.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial

variable {R : Type*} [CommRing R] {M m : ℕ}

/-- A cyclotomic zero of invertible order has exact order in every field image. -/
theorem primitiveRoot_map_of_cyclotomic {K : Type*} [Field K] (f : R →+* K) {ξ : R}
    (hξ : (cyclotomic M R).IsRoot ξ) (hu : IsUnit (M : R)) : IsPrimitiveRoot (f ξ) M := by
  let : NeZero (M : K) := ⟨by simpa using (hu.map f).ne_zero⟩
  apply isRoot_cyclotomic_iff.mp
  change (cyclotomic M K).eval (f ξ) = 0
  rw [cyclotomic.eval_apply, hξ.eq_zero, map_zero]

/-- The powered cyclotomic coordinate gives all nodes of the divisor-length transform.
Distinct powers differ by units, without a domain assumption on the cyclotomic algebra. -/
theorem cyclotomicNodePowers {ξ : R} (hξ : (cyclotomic M R).IsRoot ξ)
    (hM : 0 < M) (hu : IsUnit (M : R)) (hm : m ∣ M) :
    (ξ ^ (M/m)) ^ m = 1 ∧
      ∀ i j : Fin m, i ≠ j → IsUnit ((ξ^(M/m))^i.val - (ξ^(M/m))^j.val) := by
  have hprod : M/m*m = M := Nat.div_mul_cancel hm
  constructor
  · rw [← pow_mul, hprod]
    exact isRoot_of_unity_of_root_cyclotomic (Nat.mem_divisors.mpr ⟨dvd_rfl, hM.ne'⟩) hξ
  · intro i j hij
    by_contra h
    obtain ⟨I, hI, hi⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr h)
    let := hI
    let := Ideal.Quotient.field I
    let f := Ideal.Quotient.mk I
    have hprim := (primitiveRoot_map_of_cyclotomic f hξ hu).pow hM hprod.symm
    have he : f ((ξ^(M/m))^i.val - (ξ^(M/m))^j.val) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hi
    simp only [map_sub, map_pow, sub_eq_zero] at he
    exact hij (Fin.ext (hprim.pow_inj i.isLt j.isLt he))

/-- The cyclotomic coefficient algebra `𝒪` in the integral descent. -/
abbrev CyclotomicCoefficients (S : Type*) [CommRing S] (M : ℕ) := AdjoinRoot (cyclotomic M S)

/-- The image of the adjoined cyclotomic coordinate satisfies its defining polynomial
over any target ring. -/
theorem cyclotomicCoordinate_isRoot (S : Type*) [CommRing S] (M : ℕ)
    (f : CyclotomicCoefficients S M →+* R) :
    (cyclotomic M R).IsRoot (f (AdjoinRoot.root (cyclotomic M S))) := by
  have hx := AdjoinRoot.isRoot_root (cyclotomic M S)
  rw [map_cyclotomic] at hx
  change (cyclotomic M R).eval (f _) = 0
  rw [cyclotomic.eval_apply, hx.eq_zero, map_zero]

/-- The two-local base and its quadratic order in the primitive cube root. -/
abbrev TwoLocalBase := protectedRationals {2}
abbrev TwoLocalQuadratic := CyclotomicCoefficients TwoLocalBase 3

/-- The length-`h` jet over the manuscript's two successive cyclotomic algebras. -/
abbrev IntegralJet (M h : ℕ) := AdjoinRoot ((X : (CyclotomicCoefficients TwoLocalQuadratic M)[X]) ^ h)

noncomputable section

/-- Cyclotomic coordinate in the finite jet. -/
def jetCyclotomicCoordinate (M h : ℕ) : IntegralJet M h :=
  algebraMap (CyclotomicCoefficients TwoLocalQuadratic M) (IntegralJet M h)
    (AdjoinRoot.root (cyclotomic M TwoLocalQuadratic))

private theorem isUnit_odd_twoLocal {k : ℕ} (hk : Odd k) : IsUnit (k : TwoLocalBase) :=
  isUnit_natCast_protectedRationals hk.pos.ne' (by
    intro p hp
    simp only [Finset.mem_singleton] at hp
    simpa only [hp] using Nat.coprime_two_left.mpr hk)

/-- All odd integer scalars are units in the jet, in particular the binomial derivatives. -/
theorem isUnit_odd_inIntegralJet (M h : ℕ) {k : ℕ} (hk : Odd k) :
    IsUnit (k : IntegralJet M h) := by
  have hS := (isUnit_odd_twoLocal hk).map (algebraMap TwoLocalBase TwoLocalQuadratic)
  have hO := hS.map (algebraMap TwoLocalQuadratic (CyclotomicCoefficients TwoLocalQuadratic M))
  simpa using hO.map (algebraMap (CyclotomicCoefficients TwoLocalQuadratic M) (IntegralJet M h))

/-- Every divisor of the odd order supplies a unit-valued system of Fourier nodes
in precisely the jet algebra used by the integral descent. -/
theorem integralJet_axisRoot {M m : ℕ} (hM : Odd M) (hm : m ∣ M) (h : ℕ) :
    ∃ u : (IntegralJet M h)ˣ, (u : IntegralJet M h) = (jetCyclotomicCoordinate M h)^(M/m) ∧
      u^m = 1 ∧ ∀ i j : Fin m, i ≠ j → IsUnit ((u : IntegralJet M h)^i.val - (u : IntegralJet M h)^j.val) := by
  have hξ := cyclotomicCoordinate_isRoot TwoLocalQuadratic M
    (algebraMap (CyclotomicCoefficients TwoLocalQuadratic M) (IntegralJet M h))
  obtain ⟨hpow, hsep⟩ := cyclotomicNodePowers hξ hM.pos
    (isUnit_odd_inIntegralJet M h hM) hm
  obtain ⟨u, hu⟩ := IsUnit.of_pow_eq_one hpow (Nat.pos_of_dvd_of_pos hm hM.pos).ne'
  exact ⟨u, hu, Units.ext (by simpa only [Units.val_pow_eq_pow_val, Units.val_one, hu] using hpow),
    by simpa only [hu] using hsep⟩

/-- Every divisor root retains its order modulo every maximal ideal. In particular a
divisible ninth root meets the residue-field hypothesis of the ternary word construction. -/
theorem integralJet_axisRoot_primitive_residue {M m : ℕ} (hM : Odd M) (hm : m ∣ M)
    (h : ℕ) (I : MaximalSpectrum (IntegralJet M h)) :
    IsPrimitiveRoot (Ideal.Quotient.mk I.asIdeal ((jetCyclotomicCoordinate M h)^(M/m))) m := by
  let := Ideal.Quotient.field I.asIdeal
  have hξ := cyclotomicCoordinate_isRoot TwoLocalQuadratic M
    (algebraMap (CyclotomicCoefficients TwoLocalQuadratic M) (IntegralJet M h))
  have hprim := primitiveRoot_map_of_cyclotomic (Ideal.Quotient.mk I.asIdeal) hξ
    (isUnit_odd_inIntegralJet M h hM)
  rw [map_pow]
  exact hprim.pow hM.pos (Nat.div_mul_cancel hm).symm

/-- All coefficient and jet extensions are finite over the preceding semilocal ring. -/
theorem integralJet_semilocal (M h : ℕ) : Finite (MaximalSpectrum (IntegralJet M h)) := by
  let : Finite (MaximalSpectrum TwoLocalBase) :=
    finite_maximalSpectrum_protectedRationals (by simp [Nat.prime_two])
  let := (cyclotomic.monic 3 TwoLocalBase).finite_adjoinRoot
  let := finite_maximalSpectrum_of_finite_algebra TwoLocalBase TwoLocalQuadratic
  let := (cyclotomic.monic M TwoLocalQuadratic).finite_adjoinRoot
  let := finite_maximalSpectrum_of_finite_algebra TwoLocalQuadratic (CyclotomicCoefficients TwoLocalQuadratic M)
  let := (monic_X_pow (R := CyclotomicCoefficients TwoLocalQuadratic M) h).finite_adjoinRoot
  exact finite_maximalSpectrum_of_finite_algebra (CyclotomicCoefficients TwoLocalQuadratic M) (IntegralJet M h)

/-- The primitive cubic generator of the first (quadratic) extension, viewed in the jet. -/
def jetCubeRoot (M h : ℕ) : IntegralJet M h :=
  ((algebraMap (CyclotomicCoefficients TwoLocalQuadratic M) (IntegralJet M h)).comp
    (algebraMap TwoLocalQuadratic (CyclotomicCoefficients TwoLocalQuadratic M)))
    (AdjoinRoot.root (cyclotomic 3 TwoLocalBase))

theorem jetCubeRoot_isRoot (M h : ℕ) :
    (cyclotomic 3 (IntegralJet M h)).IsRoot (jetCubeRoot M h) :=
  cyclotomicCoordinate_isRoot _ _ _

/-- The original ternary Fourier coordinate is primitive in every residue field. -/
theorem jetCubeRoot_primitive_residue (M h : ℕ) (I : MaximalSpectrum (IntegralJet M h)) :
    IsPrimitiveRoot (Ideal.Quotient.mk I.asIdeal (jetCubeRoot M h)) 3 := by
  let := Ideal.Quotient.field I.asIdeal
  exact primitiveRoot_map_of_cyclotomic (Ideal.Quotient.mk I.asIdeal) (jetCubeRoot_isRoot M h)
    (isUnit_odd_inIntegralJet M h (show Odd 3 by decide))

/-- Each shear coefficient in the two-local jet is a sum of two units. In each
residue field one and the nontrivial cube root give two choices for the first unit. -/
theorem integralJet_unit_split (M h : ℕ) (x : IntegralJet M h) :
    ∃ s : IntegralJet M h, IsUnit s ∧ IsUnit (x-s) := by
  let := integralJet_semilocal M h
  obtain ⟨hpow, hsep⟩ := cyclotomicNodePowers (jetCubeRoot_isRoot M h) (by decide)
    (isUnit_odd_inIntegralJet M h (by decide : Odd 3)) (dvd_refl 3)
  apply exists_unit_split_of_third_residue (b := jetCubeRoot M h) _ _ x
  · apply IsUnit.of_pow_eq_one (n := 3) _ (by decide)
    simpa using hpow
  · simpa using hsep (1 : Fin 3) 0 (by decide)

end

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI

import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-! # Coefficients for the integral prime Fourier kernel

Adjoining a zero of the prime cyclotomic polynomial to the integers with
the radix inverted gives one coefficient ring for a whole family of
transforms. Its universal property specializes a circuit even to rings
with zero divisors.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial

/-- Integers with the radix inverted. -/
abbrev PrimeRadixBase (p : ℕ) := Localization.Away (p : ℤ)

/-- The companion's coefficient ring for radix `p`. -/
abbrev PrimeCoefficientRing (p : ℕ) := AdjoinRoot (cyclotomic p (PrimeRadixBase p))

noncomputable abbrev primeCoefficientRoot (p : ℕ) : PrimeCoefficientRing p :=
  AdjoinRoot.root _

private noncomputable def radixHom {R : Type*} [CommRing R] {p : ℕ} (hp : IsUnit (p : R)) :
    PrimeRadixBase p →+* R :=
  IsLocalization.Away.lift (p : ℤ) (g := Int.castRingHom R) (by simpa using hp)

private theorem radixBase_nontrivial (p : ℕ) [Fact p.Prime] : Nontrivial (PrimeRadixBase p) :=
  (radixHom (p := p) (R := ℚ) (isUnit_iff_ne_zero.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero))).domain_nontrivial

instance (p : ℕ) [Fact p.Prime] : Nontrivial (PrimeCoefficientRing p) := by
  let := radixBase_nontrivial p
  apply (AdjoinRoot.nontrivial_iff_of_monic (cyclotomic.monic p _)).mpr
  rw [← natDegree_pos_iff_degree_pos, natDegree_cyclotomic]
  exact Nat.totient_pos.mpr (Fact.out : p.Prime).pos

theorem primeCoefficientRing_radix_unit (p : ℕ) : IsUnit (p : PrimeCoefficientRing p) := by
  have h : IsUnit (p : PrimeRadixBase p) := by
    simpa using (IsLocalization.Away.algebraMap_isUnit (S := PrimeRadixBase p) (p : ℤ))
  simpa using h.map (algebraMap (PrimeRadixBase p) (PrimeCoefficientRing p))

theorem primeCoefficientRoot_sum (p : ℕ) [Fact p.Prime] :
    ∑ i ∈ Finset.range p, primeCoefficientRoot p ^ i = 0 := by
  have h := AdjoinRoot.eval₂_root (cyclotomic p (PrimeRadixBase p))
  simpa only [cyclotomic_prime, eval₂_finsetSum, eval₂_pow, eval₂_X] using h

theorem primeCoefficientRoot_pow (p : ℕ) [Fact p.Prime] : primeCoefficientRoot p ^ p = 1 := by
  apply sub_eq_zero.mp
  rw [← geom_sum_mul, primeCoefficientRoot_sum, zero_mul]

theorem primeCoefficientRoot_primitive (p : ℕ) [Fact p.Prime] :
    IsPrimitiveRoot (primeCoefficientRoot p) p := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_prime
  · exact primeCoefficientRoot_pow p
  · intro h
    have he := primeCoefficientRoot_sum p
    simp only [h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at he
    exact (primeCoefficientRing_radix_unit p).ne_zero he

/-- Specialization is determined by the chosen cyclotomic root. -/
noncomputable def primeCoefficientHom {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime]
    (ζ : R) (hp : IsUnit (p : R)) (hsum : ∑ i ∈ Finset.range p, ζ ^ i = 0) :
    PrimeCoefficientRing p →+* R :=
  AdjoinRoot.lift (radixHom hp) ζ (by
    simpa only [cyclotomic_prime, eval₂_finsetSum, eval₂_pow, eval₂_X] using hsum)

@[simp] theorem primeCoefficientHom_root {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime]
    (ζ : R) (hp : IsUnit (p : R)) (hsum : ∑ i ∈ Finset.range p, ζ ^ i = 0) :
    primeCoefficientHom ζ hp hsum (primeCoefficientRoot p) = ζ :=
  AdjoinRoot.lift_root _

end FiniteFourier
end LinearAlgebra
end OAI

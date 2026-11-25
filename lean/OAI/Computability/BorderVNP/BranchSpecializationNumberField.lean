import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Good reduction of the fixed tensor constants

For a fixed tuple in a number field and a finite list of polynomial
nonvanishings, one integer clears denominators of the tuple and of the
reciprocals of the nonvanishings. At every prime away from this integer,
reducing the localized ring of integers preserves every polynomial identity
and every specified nonvanishing. The residue field has degree at most that
of the original number field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Specialization

open NumberField MvPolynomial
open scoped NumberField

universe u

/-- A prime of the ring of integers over `p` supplies a finite residue
field of cardinality at most `p^[K:ℚ]`. -/
theorem exists_residue_field (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (hp : p.Prime) :
    ∃ (E : Type u) (_ : Field E) (_ : CharP E p) (_ : Finite E),
      Nat.card E ≤ p ^ Module.finrank ℚ K ∧ Nonempty (𝓞 K →+* E) := by
  have hz := Nat.prime_iff_prime_int.mp hp
  have : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hz.ne_zero).mpr hz).isMaximal (by simpa using hz.ne_zero)
  obtain ⟨P, hmax, hP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K)
    (Ideal.span {(p : ℤ)}) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))]
      exact bot_le)
  let E := 𝓞 K ⧸ P
  let : Field E := Ideal.Quotient.field P
  have hmem : (p : 𝓞 K) ∈ P := by
    have h : (p : ℤ) ∈ P.under ℤ := hP ▸ Ideal.mem_span_singleton_self (p : ℤ)
    simpa only [Ideal.under, Ideal.mem_comap, map_natCast] using h
  have hzero : (p : E) = 0 := by
    simpa only [map_natCast] using (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  refine ⟨E, inferInstance, (CharP.charP_iff_prime_eq_zero hp).mpr hzero, inferInstance, ?_,
    ⟨Ideal.Quotient.mk P⟩⟩
  have hdiv := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank] at hdiv
  simpa [Ideal.absNorm_apply, Submodule.cardQuot_apply, E] using
    Nat.le_of_dvd (pow_pos hp.pos _) hdiv

/-- Integral polynomial evaluations commute with reduction of their arguments. -/
private theorem map_eval_int {ι R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : ι → R) (q : MvPolynomial ι ℤ) :
    f (eval₂Hom (Int.castRingHom R) x q) = eval₂Hom (Int.castRingHom S) (f ∘ x) q := by
  rw [map_eval₂Hom]
  congr 2
  exact Subsingleton.elim _ _

private theorem localize_constants {K : Type u} [Field K] [NumberField K] (s : Finset K) :
    ∃ (d : ℤ) (_ : d ≠ 0)
      (emb : Localization.Away (d : 𝓞 K) →+* K), Function.Injective emb ∧
        ∀ x ∈ s, x ∈ Set.range emb := by
  obtain ⟨d, hd, hds⟩ := exists_integral_multiples ℤ ℚ s
  let L := Localization.Away (d : 𝓞 K)
  let j := algebraMap (𝓞 K) K
  have hunit : IsUnit (j (d : 𝓞 K)) := by
    rw [map_intCast]
    exact isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hd)
  let emb : L →+* K := IsLocalization.Away.lift _ hunit
  have hbase (z : 𝓞 K) : emb (algebraMap (𝓞 K) L z) = j z := IsLocalization.Away.lift_eq _ _ _
  have hinj : Function.Injective emb := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (d : 𝓞 K)) emb).mpr
    intro x y
    constructor
    · exact congrArg emb
    · intro h
      rw [hbase, hbase] at h
      exact congrArg (algebraMap (𝓞 K) L) (Subtype.val_injective h)
  refine ⟨d, hd, emb, hinj, ?_⟩
  intro x hx
  let z : 𝓞 K := ⟨d • x, hds x hx⟩
  let inv : L := IsLocalization.Away.invSelf (d : 𝓞 K)
  have he : (d : K) * emb inv = 1 := by
    have h := congrArg emb (IsLocalization.Away.mul_invSelf (S := L) (d : 𝓞 K))
    simpa only [map_mul, hbase, map_intCast, map_one] using h
  refine ⟨algebraMap (𝓞 K) L z * inv, ?_⟩
  rw [map_mul, hbase]
  change (d • x) * emb inv = x
  rw [zsmul_eq_mul, mul_comm (d : K) x, mul_assoc, he, mul_one]

/-- Lemma 9.1 for fixed number-field constants. Outside the divisors of one
nonzero integer there is a common reduction of the tuple preserving all its
integral polynomial relations and the prescribed finite list of nonvanishings. -/
theorem exists_good_reduction {ι : Type*} [Fintype ι]
    (K : Type u) [Field K] [NumberField K] (x : ι → K)
    (tests : Finset (MvPolynomial ι ℤ))
    (htests : ∀ q ∈ tests, eval₂Hom (Int.castRingHom K) x q ≠ 0) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ p : ℕ, p.Prime → (¬ (p : ℤ) ∣ d) →
      ∃ (E : Type u) (_ : Field E) (_ : CharP E p) (_ : Finite E) (x' : ι → E),
        Nat.card E ≤ p ^ Module.finrank ℚ K ∧
        (∀ q : MvPolynomial ι ℤ, eval₂Hom (Int.castRingHom K) x q = 0 →
          eval₂Hom (Int.castRingHom E) x' q = 0) ∧
        ∀ q ∈ tests, eval₂Hom (Int.castRingHom E) x' q ≠ 0 := by
  classical
  let invTest := fun q => (eval₂Hom (Int.castRingHom K) x q)⁻¹
  let s := Finset.univ.image x ∪ tests.image invTest
  obtain ⟨d, hd, emb, hinj, hrange⟩ := localize_constants s
  let L := Localization.Away (d : 𝓞 K)
  choose y hy using fun i => hrange (x i) (Finset.mem_union_left _ (Finset.mem_image_of_mem x (Finset.mem_univ i)))
  have htuple : emb ∘ y = x := funext hy
  have hval (q : MvPolynomial ι ℤ) :
      emb (eval₂Hom (Int.castRingHom L) y q) = eval₂Hom (Int.castRingHom K) x q := by
    rw [map_eval_int, htuple]
  refine ⟨d, hd, ?_⟩
  intro p hp hpd
  obtain ⟨E, fE, cE, finE, hcard, ⟨g⟩⟩ := exists_residue_field K p hp
  have hg : IsUnit (g (d : 𝓞 K)) := by
    rw [map_intCast, isUnit_iff_ne_zero]
    exact fun h => hpd ((CharP.intCast_eq_zero_iff E p d).mp h)
  let red : L →+* E := IsLocalization.Away.lift _ hg
  refine ⟨E, fE, cE, finE, red ∘ y, hcard, ?_, ?_⟩
  · intro q hq
    have hz : eval₂Hom (Int.castRingHom L) y q = 0 := hinj ((hval q).trans (hq.trans (map_zero emb).symm))
    rw [← map_eval_int, hz, map_zero]
  · intro q hq
    obtain ⟨w, hw⟩ := hrange (invTest q) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hq))
    have hunit : eval₂Hom (Int.castRingHom L) y q * w = 1 := by
      apply hinj
      rw [map_mul, map_one, hval, hw]
      exact mul_inv_cancel₀ (htests q hq)
    have h := congrArg red hunit
    rw [map_mul, map_one, map_eval_int] at h
    exact left_ne_zero_of_mul (h ▸ one_ne_zero)

end Specialization

end BorderVNP
end Computability
end OAI

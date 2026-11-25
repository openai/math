import OAI.Computability.BorderVNP.BranchSpecializationNumberField
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Descending the fixed identities to a number field

A tuple in an arbitrary characteristic-zero field may have transcendental
entries. Its polynomial identities and finitely many required nonvanishings
can first be realized in a number field. This permits the good reduction used
in Lemma 9.1 without an algebraicity assumption on the original constants.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Specialization

open MvPolynomial

universe u v

/-- Over any base field, a tuple with a finite list of required inequations
specializes into a finite extension, preserving all its integral equations. -/
theorem exists_finiteExtension_realization {ι : Type u} [Fintype ι]
    (F : Type v) [Field F] (K : Type*) [Field K] [Algebra F K] (x : ι → K)
    (tests : Finset (MvPolynomial ι ℤ))
    (htests : ∀ q ∈ tests, eval₂Hom (Int.castRingHom K) x q ≠ 0) :
    ∃ (L : Type (max u v)) (_ : Field L) (_ : Algebra F L) (_ : Module.Finite F L) (y : ι → L),
      (∀ q : MvPolynomial ι ℤ, eval₂Hom (Int.castRingHom K) x q = 0 →
        eval₂Hom (Int.castRingHom L) y q = 0) ∧
      ∀ q ∈ tests, eval₂Hom (Int.castRingHom L) y q ≠ 0 := by
  classical
  let T := ι ⊕ ↥tests
  let A := MvPolynomial T F
  let vars : ι → A := X ∘ Sum.inl
  let lift := eval₂Hom (Int.castRingHom A) vars
  let f : A →+* K := eval₂Hom (algebraMap F K) (Sum.elim x (fun q => (eval₂Hom (Int.castRingHom K) x q.val)⁻¹))
  have hf (q : MvPolynomial ι ℤ) : f (lift q) = eval₂Hom (Int.castRingHom K) x q := by
    rw [show lift q = eval₂Hom _ vars q from rfl, map_eval₂Hom]
    congr 2
    · exact Subsingleton.elim _ _
    · funext i
      exact eval₂Hom_X' _ _ _
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal (RingHom.ker f) (RingHom.ker_ne_top _)
  let L := A ⧸ P
  let : Field L := Ideal.Quotient.field P
  have : Algebra.IsIntegral F L := by
    rw [← algebraMap_isIntegral_iff]
    exact comp_C_integral_of_surjective_of_isJacobsonRing (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have : Module.Finite F L := Algebra.finite_iff_isIntegral_and_finiteType.mpr ⟨inferInstance, inferInstance⟩
  let g : A →+* L := Ideal.Quotient.mk P
  let y := g ∘ vars
  have hg (q : MvPolynomial ι ℤ) : g (lift q) = eval₂Hom (Int.castRingHom L) y q := by
    rw [show lift q = eval₂Hom _ vars q from rfl, map_eval₂Hom]
    congr 2
  have desc (a : A) (ha : f a = 0) : g a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hle ha)
  refine ⟨L, inferInstance, inferInstance, inferInstance, y, fun q hq => (hg q).symm.trans (desc _ ((hf q).trans hq)), ?_⟩
  intro q hq
  let v : A := X (Sum.inr (⟨q, hq⟩ : ↥tests))
  have h : f (lift q * v - 1) = 0 := by
    rw [map_sub, map_mul, map_one, hf]
    change _ * (eval₂Hom (algebraMap F K) _ (X (Sum.inr (⟨q, hq⟩ : ↥tests)))) - 1 = 0
    rw [eval₂Hom_X']
    exact sub_eq_zero.mpr (mul_inv_cancel₀ (htests q hq))
  have h' := desc _ h
  rw [map_sub, map_mul, map_one, hg, sub_eq_zero] at h'
  exact left_ne_zero_of_mul (h' ▸ one_ne_zero)

/-- Specialization to a number field keeps every integral identity and the
prescribed nonvanishings of an arbitrary characteristic-zero tuple. -/
theorem exists_numberField_realization {ι : Type u} [Fintype ι]
    (K : Type*) [Field K] [CharZero K] (x : ι → K)
    (tests : Finset (MvPolynomial ι ℤ))
    (htests : ∀ q ∈ tests, eval₂Hom (Int.castRingHom K) x q ≠ 0) :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (y : ι → L),
      (∀ q : MvPolynomial ι ℤ, eval₂Hom (Int.castRingHom K) x q = 0 →
        eval₂Hom (Int.castRingHom L) y q = 0) ∧
      ∀ q ∈ tests, eval₂Hom (Int.castRingHom L) y q ≠ 0 := by
  obtain ⟨L, fL, _, _, y, hy, ht⟩ := exists_finiteExtension_realization ℚ K x tests htests
  exact ⟨L, fL, NumberField.of_module_finite ℚ L, y, hy, ht⟩

/-- In fixed positive characteristic, the tuple of tensor constants can be
realized over one finite field of that characteristic. -/
theorem exists_finiteField_realization {ι : Type u} [Fintype ι]
    (K : Type*) [Field K] (p : ℕ) [CharP K p] (hp : p.Prime) (x : ι → K)
    (tests : Finset (MvPolynomial ι ℤ))
    (htests : ∀ q ∈ tests, eval₂Hom (Int.castRingHom K) x q ≠ 0) :
    ∃ (L : Type u) (_ : Field L) (_ : CharP L p) (_ : Finite L) (y : ι → L),
      (∀ q : MvPolynomial ι ℤ, eval₂Hom (Int.castRingHom K) x q = 0 →
        eval₂Hom (Int.castRingHom L) y q = 0) ∧
      ∀ q ∈ tests, eval₂Hom (Int.castRingHom L) y q ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Algebra (ZMod p) K := ZMod.algebra _ _
  obtain ⟨L, fL, aL, _, y, hy, ht⟩ := exists_finiteExtension_realization (ZMod p) K x tests htests
  have hc : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
  exact ⟨L, fL, hc, Module.finite_of_finite (ZMod p), y, hy, ht⟩

/-- For constants from any characteristic-zero field, both the exclusion
integer and the extension degree bound can be chosen before the prime. -/
theorem exists_fixed_constants_reduction {ι : Type u} [Fintype ι]
    (K : Type*) [Field K] [CharZero K] (x : ι → K)
    (tests : Finset (MvPolynomial ι ℤ))
    (htests : ∀ q ∈ tests, eval₂Hom (Int.castRingHom K) x q ≠ 0) :
    ∃ (d : ℤ) (k : ℕ), d ≠ 0 ∧ ∀ p : ℕ, p.Prime → (¬ (p : ℤ) ∣ d) →
      ∃ (E : Type u) (_ : Field E) (_ : CharP E p) (_ : Finite E) (x' : ι → E),
        Nat.card E ≤ p ^ k ∧
        (∀ q : MvPolynomial ι ℤ, eval₂Hom (Int.castRingHom K) x q = 0 →
          eval₂Hom (Int.castRingHom E) x' q = 0) ∧
        ∀ q ∈ tests, eval₂Hom (Int.castRingHom E) x' q ≠ 0 := by
  obtain ⟨L, _, _, y, hy, hytests⟩ := exists_numberField_realization K x tests htests
  obtain ⟨d, hd, hred⟩ := exists_good_reduction L y tests hytests
  refine ⟨d, Module.finrank ℚ L, hd, ?_⟩
  intro p hp hpd
  obtain ⟨E, fE, cE, finE, x', hsize, heq, ht⟩ := hred p hp hpd
  exact ⟨E, fE, cE, finE, x', hsize, fun q hq => heq q (hy q hq), ht⟩

end Specialization

end BorderVNP
end Computability
end OAI

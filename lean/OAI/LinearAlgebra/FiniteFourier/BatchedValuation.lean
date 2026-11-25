import OAI.LinearAlgebra.SpectralBooks.ZariskiCurve
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Nullstellensatz

/-! # Valuative specialization of affine coordinates -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks MvPolynomial
open scoped Classical

universe u v
variable {K : Type u} [Field K] {S : Type v} {ι κ : Type}

/-- Evaluate a polynomial simultaneously at a family of affine points. -/
noncomputable def familyEval (x : S → ι → K) : MvPolynomial ι K →+* (S → K) :=
  RingHom.pi (fun s => eval (x s))

theorem familyEval_apply (x : S → ι → K) (p : MvPolynomial ι K) (s : S) :
    familyEval x p s = eval (x s) p := rfl

private theorem exists_dominating_valuation {A L : Type*} [CommRing A] [Field L]
    (g : A →+* L) (I : Ideal A) [I.IsPrime] (h : RingHom.ker g ≤ I) :
    ∃ V : ValuationSubring L, (∀ p, g p ∈ V) ∧ ∀ p ∈ I, g p ∈ V.nonunits := by
  let J := I.map g.rangeRestrict
  have hJ : J ≠ ⊤ := by
    have he : J.comap g.rangeRestrict = I := by
      rw [Ideal.comap_map_of_surjective _ g.rangeRestrict_surjective, sup_eq_left]
      intro p hp
      apply h
      exact congrArg Subtype.val (RingHom.mem_ker.mp hp)
    intro ht
    exact (inferInstance : I.IsPrime).ne_top (he.symm.trans (by rw [ht, Ideal.comap_top]))
  obtain ⟨V, hV, hm⟩ := Ideal.image_subset_nonunits_valuationSubring J hJ
  exact ⟨V, fun p => hV ⟨p, rfl⟩, fun p hp =>
    hm ⟨g.rangeRestrict p, Ideal.mem_map_of_mem _ hp, rfl⟩⟩

theorem exists_valuation_specialization (x : S → ι → K) (x₀ : ι → K)
    (hx : x₀ ∈ affineZariskiClosure (Set.range x)) :
    ∃ (L : Type (max u v)) (_ : Field L) (f : (S → K) →+* L) (V : ValuationSubring L),
      (∀ p, f (familyEval x p) ∈ V) ∧
      ∀ p, eval x₀ p = 0 → f (familyEval x p) ∈ V.nonunits := by
  let I := RingHom.ker (eval x₀)
  have hI : I.IsPrime := RingHom.ker_isPrime _
  have hle : (⊥ : Ideal (S → K)).comap (familyEval x) ≤ I := by
    intro p hp
    have he : familyEval x p = 0 := hp
    apply hx p
    rintro _ ⟨s, rfl⟩
    exact congrFun he s
  obtain ⟨J, _, hJ, hJI⟩ := Ideal.exists_ideal_comap_le_prime I _ hle
  let L := FractionRing ((S → K) ⧸ J)
  let f := (algebraMap ((S → K) ⧸ J) L).comp (Ideal.Quotient.mk J)
  have hf : RingHom.ker (f.comp (familyEval x)) ≤ I := by
    intro p hp
    apply hJI
    change familyEval x p ∈ J
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective ((S → K) ⧸ J) L
    rw [map_zero]
    exact hp
  obtain ⟨V, hV, hm⟩ := exists_dominating_valuation _ I hf
  exact ⟨L, inferInstance, f, V, hV, hm⟩

theorem exists_residue_tuple [Finite ι] [IsAlgClosed K] {L : Type*} [Field L]
    (f : (S → K) →+* L) (V : ValuationSubring L) (x : S → ι → K)
    (hc : ∀ c : K, f (fun _ => c) ∈ V) (hx : ∀ i, f (fun s => x s i) ∈ V) :
    ∃ z : ι → K, ∀ p, f (familyEval x p) ∈ V.nonunits → eval z p = 0 := by
  have hb (p : MvPolynomial ι K) : f (familyEval x p) ∈ V := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [show familyEval x (C c) = fun _ => c from funext fun s => by simp [familyEval_apply]]
      exact hc c
    | add p q hp hq => rw [map_add, map_add]; exact V.toSubring.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, map_mul, show familyEval x (X i) = fun s => x s i from
        funext fun s => by simp [familyEval_apply]]
      exact V.toSubring.mul_mem hp (hx i)
  let g := (f.comp (familyEval x)).codRestrict V.toSubring hb
  let I := (IsLocalRing.maximalIdeal V).comap g
  have hI : I ≠ ⊤ := Ideal.comap_ne_top g (IsLocalRing.maximalIdeal.isMaximal V).ne_top
  obtain ⟨J, hJ, hIJ⟩ := I.exists_le_maximal hI
  obtain ⟨z, hz⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hJ
  refine ⟨z, fun p hp => (MvPolynomial.mem_vanishingIdeal_singleton_iff z p).mp ?_⟩
  rw [← hz]
  exact hIJ (V.coe_mem_nonunits_iff.mp hp : g p ∈ IsLocalRing.maximalIdeal V)

end FiniteFourier
end LinearAlgebra
end OAI

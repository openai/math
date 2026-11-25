import OAI.Computability.BorderVNP.Model
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Simultaneous specialization of all output coefficients

For a polynomial table over an infinite field, membership in its affine image
closure is equivalent to simultaneous specialization in one valuation ring of
the field of rational functions in the parameters. The valuation is allowed to
have arbitrary rank. Section 9.2 additionally needs a one-dimensional branch
of bounded degree for the residue algorithm.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

/-- A point satisfying all relations on a subring of a field has a valuation
ring in that field taking its vanishing ideal into the maximal ideal. -/
theorem valuationRing_of_kernel_le {R K L : Type*} [CommRing R] [Field K] [Field L]
    (f : R →+* L) (g : R →+* K) (h : RingHom.ker f ≤ RingHom.ker g) :
    ∃ V : ValuationSubring L, f.range ≤ V.toSubring ∧
      ∀ r : R, g r = 0 → f r ∈ V.nonunits := by
  let specialization : f.range →+* K :=
    (Ideal.Quotient.lift (RingHom.ker f) g (fun r hr => h hr)).comp
      f.quotientKerEquivRange.symm.toRingHom
  have apply_specialization (r : R) : specialization (f.rangeRestrict r) = g r := by
    change (Ideal.Quotient.lift (RingHom.ker f) g (fun _ hr => h hr))
      (f.quotientKerEquivRange.symm (f.rangeRestrict r)) = g r
    have he : f.quotientKerEquivRange (Ideal.Quotient.mk (RingHom.ker f) r) = f.rangeRestrict r :=
      rfl
    rw [← he, RingEquiv.symm_apply_apply]
    rfl
  obtain ⟨V, hV, hm⟩ := Ideal.image_subset_nonunits_valuationSubring
    (RingHom.ker specialization) (RingHom.ker_ne_top specialization)
  refine ⟨V, hV, fun r hr => hm ⟨f.rangeRestrict r, ?_, rfl⟩⟩
  exact (apply_specialization r).trans hr

/-- Generic parameters in their rational function field. -/
abbrev ParameterField (σ K : Type*) [Field K] := FractionRing (MvPolynomial σ K)

/-- Inclusion of the polynomial table entries into the parameter field. -/
noncomputable def genericTable {σ ι K : Type*} [Field K] (Y : ι → MvPolynomial σ K) :
    MvPolynomial ι K →+* ParameterField σ K :=
  (algebraMap _ _).comp (eval₂Hom C Y)

private theorem eval_table {σ ι K : Type*} [Field K] (Y : ι → MvPolynomial σ K)
    (a : σ → K) (q : MvPolynomial ι K) :
    eval a (eval₂Hom C Y q) = eval (fun i => eval a (Y i)) q := by
  change eval a (eval₂ C Y q) = _
  rw [eval_eval₂]
  have h : (eval a).comp C = RingHom.id K := by ext; simp
  rw [h, eval₂_id]

/-- The valuative characterization of polynomial image closure. All polynomials
in the outputs are regular at the same place, with the residue given by their
evaluation at the prescribed coefficient vector. -/
theorem mem_imageClosure_iff_valuation {σ ι K : Type*} [Field K] [Infinite K]
    (Y : ι → MvPolynomial σ K) (c : ι → K) :
    c ∈ imageClosure (Set.range (fun a : σ → K => fun i => eval a (Y i))) ↔
      ∃ V : ValuationSubring (ParameterField σ K), (genericTable Y).range ≤ V.toSubring ∧
        ∀ q : MvPolynomial ι K,
          genericTable Y q - genericTable Y (C (eval c q)) ∈ V.nonunits := by
  let inc := algebraMap (MvPolynomial σ K) (ParameterField σ K)
  have hi : Function.Injective inc := IsFractionRing.injective _ _
  constructor
  · intro hc
    have hker : RingHom.ker (genericTable Y) ≤ RingHom.ker (eval c) := by
      intro q hq
      change eval c q = 0
      apply hc q
      rintro _ ⟨a, rfl⟩
      rw [← eval_table]
      change inc (eval₂Hom C Y q) = 0 at hq
      have h : eval₂Hom C Y q = 0 := hi (hq.trans (map_zero inc).symm)
      rw [h, map_zero]
    obtain ⟨V, hV, hres⟩ := valuationRing_of_kernel_le (genericTable Y) (eval c) hker
    refine ⟨V, hV, fun q => ?_⟩
    rw [← map_sub]
    exact hres (q - C (eval c q)) (by simp)
  · rintro ⟨V, _, hres⟩ q hq
    have hz : eval₂Hom C Y q = 0 := MvPolynomial.funext fun a => by
      rw [map_zero, eval_table]
      exact hq _ ⟨a, rfl⟩
    by_contra h
    let u := C (eval c q)⁻¹ * q
    have hu : eval c u = 1 := by simp [u, h]
    have hgu : genericTable Y u = 0 := by
      change inc (eval₂Hom C Y (C (eval c q)⁻¹ * q)) = 0
      rw [map_mul, hz, mul_zero, map_zero]
    have hm := hres u
    rw [hu, map_one, hgu, zero_sub] at hm
    have h1 : (1 : ParameterField σ K) ∈ V.nonunits := by simpa using V.nonunits.neg_mem hm
    simp [ValuationSubring.mem_nonunits_iff] at h1

end Branch

end BorderVNP
end Computability
end OAI

import OAI.Hierarchy.DegreeBorder
import OAI.Computability.BorderVNP.ModelExtension
import Mathlib.Algebra.MvPolynomial.Funext

namespace OAI
/-! # Extending scalars in degree-component border models

A polynomial parameterization allows the equations vanishing on an infinite
ground field to pass to an extension. Specializing the parameters back to
the ground field must preserve the original size budget.
-/

namespace Hierarchy

open MvPolynomial Computability.BorderVNP

variable {σ K E : Type*} [Field K] [Field E] [Algebra K E]

/-- Realize all outputs of the model over the extension by substituting
scalar parameters in a generic polynomial. Every substitution in the
ground field produces an output at the same size. -/
def HasScalarParameters (small : ℕ → MvPolynomial σ K → Prop) (large : ℕ → MvPolynomial σ E → Prop)
    (s : ℕ) : Prop :=
  ∀ p, large s p → ∃ G : MvPolynomial σ (MvPolynomial E K),
    (∀ z : E → K, small s (map (eval z) G)) ∧
    map (aeval (id : E → E)).toRingHom G = p

private theorem specialize_coeffVector {k e a τ : Type*} [Field k] [Field a] {d : ℕ}
    (G : MvPolynomial τ (MvPolynomial e k)) (t : MvPolynomial (DegreeMonomial τ d) k)
    (h : MvPolynomial e k →+* a) :
    eval₂ (h.comp C) (coeffVector d (map h G)) t = h (eval₂ C (coeffVector d G) t) := by
  rw [coeffVector_map, hom_eval₂]
  rfl

private theorem equation_baseChange [Infinite K] {d s : ℕ}
    {small : ℕ → MvPolynomial σ K → Prop} {large : ℕ → MvPolynomial σ E → Prop}
    (params : HasScalarParameters small large s) (t : MvPolynomial (DegreeMonomial σ d) K)
    (ground : ∀ g, small s g → eval (coeffVector d g) t = 0)
    (p : MvPolynomial σ E) (hp : large s p) : eval (coeffVector d p) (map (algebraMap K E) t) = 0 := by
  obtain ⟨G, atGround, recover⟩ := params p hp
  let u := eval₂ C (coeffVector d G) t
  have hu : u = 0 := by
    apply MvPolynomial.funext
    intro z
    rw [map_zero, ← specialize_coeffVector G t (eval z)]
    have hc : (eval z).comp C = RingHom.id K := by ext x; simp
    simpa only [hc, eval₂_id] using ground _ (atGround z)
  let h := (aeval (id : E → E) : MvPolynomial E K →ₐ[K] E).toRingHom
  have hc : h.comp C = algebraMap K E := by ext x; simp [h]
  rw [← recover, eval_map, ← hc, specialize_coeffVector]
  change h u = 0
  rw [hu, map_zero]

/-- An exact model over an infinite field and its scalar extension have the same
degree-component border bound on every polynomial over the ground field. -/
theorem degreeModelClosure_map_iff [Infinite K] {d s : ℕ}
    {small : ℕ → MvPolynomial σ K → Prop} {large : ℕ → MvPolynomial σ E → Prop}
    (extend : ∀ g, small s g → large s (map (algebraMap K E) g))
    (params : HasScalarParameters small large s) (p : MvPolynomial σ K) :
    coeffVector d (map (algebraMap K E) p) ∈ degreeModelClosure large d s ↔
      coeffVector d p ∈ degreeModelClosure small d s := by
  constructor
  · intro member t ht
    have he := member (map (algebraMap K E) t) (by
      rintro _ ⟨g, hg, rfl⟩
      exact equation_baseChange params t (fun f hf => ht _ ⟨f, hf, rfl⟩) g hg)
    rw [coeffVector_map, ← map_eval] at he
    exact (algebraMap K E).injective (he.trans (map_zero _).symm)
  · intro member
    rw [coeffVector_map]
    apply map_mem_imageClosure _ member
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨_, extend g hg, coeffVector_map _ _ _⟩

/-- Passing to algebraic closures removes the infinitude condition on the
original coefficient field, including finite fields. -/
theorem degreeBorderAtMost_map_iff_of_closure
    {small : ℕ → MvPolynomial σ (AlgebraicClosure K) → Prop}
    {large : ℕ → MvPolynomial σ (AlgebraicClosure E) → Prop}
    {d s : ℕ} (p : MvPolynomial σ K)
    (compare : ∀ [Algebra (AlgebraicClosure K) (AlgebraicClosure E)]
      (g : MvPolynomial σ (AlgebraicClosure K)),
      coeffVector d (map (algebraMap (AlgebraicClosure K) (AlgebraicClosure E)) g) ∈
        degreeModelClosure large d s ↔ coeffVector d g ∈ degreeModelClosure small d s) :
    DegreeBorderAtMost large d s (map (algebraMap K E) p) ↔ DegreeBorderAtMost small d s p := by
  let : Algebra K (AlgebraicClosure E) := ((algebraMap E (AlgebraicClosure E)).comp
    (algebraMap K E)).toAlgebra
  let i : AlgebraicClosure K →ₐ[K] AlgebraicClosure E := IsAlgClosed.lift
  let : Algebra (AlgebraicClosure K) (AlgebraicClosure E) := i.toRingHom.toAlgebra
  have hcomp : (algebraMap (AlgebraicClosure K) (AlgebraicClosure E)).comp
      (algebraMap K (AlgebraicClosure K)) = (algebraMap E (AlgebraicClosure E)).comp
      (algebraMap K E) := by
    ext x
    exact i.commutes x
  simpa only [DegreeBorderAtMost, map_map, hcomp] using
    compare (map (algebraMap K (AlgebraicClosure K)) p)

end Hierarchy

end OAI

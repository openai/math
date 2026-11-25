import OAI.Computability.BorderVNP.OrderedIntervalMap
import OAI.Computability.BorderVNP.ModelBaseChange

/-!
# Characteristic invariance of ordered border size

The constants of a fixed ordered circuit may be replaced by independent scalar
parameters. An equation for its degree component over an infinite field therefore
continues to hold over every extension. This permits the two-cut dichotomy to be
run over a single algebraic closure for each characteristic.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Ordered

open MvPolynomial
open VPVNP

/-- Extending the scalars of a circuit extends each formal word coefficient. -/
theorem coefficients_mapConstants {R S σ : Type*} [CommRing R] [CommRing S] {m : ℕ}
    (d : ℕ) (c : Circuit R σ m) (f : R →+* S) :
    coefficients d (output (c.mapConstants f)) = f ∘ coefficients d (output c) := by
  let h := MonoidAlgebra.mapRingHom (FreeMonoid σ) f
  have he : output (c.mapConstants f) = h (output c) := by
    unfold output Circuit.mapConstants
    rw [Circuit.eval_subst, Circuit.eval_hom]
    congr 1
    · funext r
      simp [h]
    · funext i
      simp [h]
  rw [he]
  funext a
  exact MonoidAlgebra.coeff_mapRingHom f _ _

private theorem eval_generic_word {K T α σ : Type*} [Field K] [CommRing T] {m d : ℕ}
    (c : Circuit (MvPolynomial α K) σ m) (t : MvPolynomial (Fin d → σ) K)
    (f : MvPolynomial α K →+* T) :
    eval₂ (f.comp C) (coefficients d (output (c.mapConstants f))) t =
      f (eval₂ C (coefficients d (output c)) t) := by
  rw [hom_eval₂, coefficients_mapConstants]
  rfl

variable {K E σ : Type*} [Field K] [Field E] [Algebra K E]

/-- Polynomial equations for the finite-gate image over an infinite field remain
valid after extending the scalar labels and coefficients. -/
theorem degreeImage_equation_extend [Infinite K] {d s : ℕ}
    (t : MvPolynomial (Fin d → σ) K)
    (ht : ∀ v ∈ degreeImage K σ d s, eval v t = 0) :
    ∀ v ∈ degreeImage E σ d s, eval v (map (algebraMap K E) t) = 0 := by
  rintro _ ⟨m, hm, c, rfl⟩
  let g := c.mapConstants (X : E → MvPolynomial E K)
  let u := eval₂ C (coefficients d (output g)) t
  have hu : u = 0 := by
    apply MvPolynomial.funext
    intro a
    rw [map_zero, ← eval_generic_word g t (eval a)]
    have ha : (eval a).comp C = RingHom.id K := by ext z; simp
    simpa only [ha, eval₂_id] using ht _ ⟨m, hm, g.mapConstants (eval a), rfl⟩
  let f := (aeval (id : E → E) : MvPolynomial E K →ₐ[K] E).toRingHom
  have hc : g.mapConstants f = c := by
    rw [Circuit.mapConstants_comp]
    apply Circuit.mapConstants_self
    intro x _
    simp [f]
  have hf : f.comp C = algebraMap K E := by ext x; simp [f]
  rw [eval_map, ← hf, ← hc, eval_generic_word]
  change f u = 0
  rw [hu, map_zero]

/-- Closure membership for a word coefficient vector over an infinite ground
field is invariant under extension of the ambient field. -/
theorem degreeImage_closure_extend_iff [Infinite K] {d s : ℕ} (v : (Fin d → σ) → K) :
    (algebraMap K E ∘ v) ∈ imageClosure (degreeImage E σ d s) ↔
    v ∈ imageClosure (degreeImage K σ d s) := by
  constructor
  · intro h t ht
    have he := h (map (algebraMap K E) t) (degreeImage_equation_extend t ht)
    rw [← map_eval] at he
    exact (algebraMap K E).injective (he.trans (map_zero _).symm)
  · apply map_mem_imageClosure
    rintro _ ⟨m, hm, c, rfl⟩
    exact ⟨m, hm, c.mapConstants (algebraMap K E), coefficients_mapConstants ..⟩

private theorem rowImage_extend_iff [Infinite K] (n s : ℕ) (signed : Bool) :
    coefficients n (rowPolynomial E n signed) ∈ imageClosure (degreeImage E _ n s) ↔
      coefficients n (rowPolynomial K n signed) ∈ imageClosure (degreeImage K _ n s) := by
  rw [← map_rowPolynomial (algebraMap K E) n signed]
  have he : coefficients n (MonoidAlgebra.mapRingHom _ (algebraMap K E) (rowPolynomial K n signed)) =
      algebraMap K E ∘ coefficients n (rowPolynomial K n signed) := by
    funext a
    exact MonoidAlgebra.coeff_mapRingHom ..
  rw [he, degreeImage_closure_extend_iff]

private theorem rowSize_le_iff (F : Type*) [Field F] (n s : ℕ) (signed : Bool) :
    borderSize n (rowPolynomial F n signed) ≤ s ↔
      coefficients n (rowPolynomial (AlgebraicClosure F) n signed) ∈
        imageClosure (degreeImage (AlgebraicClosure F) _ n s) := by
  rw [borderSize_le_iff, ← map_rowPolynomial (algebraMap F (AlgebraicClosure F)) n signed]
  have he : coefficients n (MonoidAlgebra.mapRingHom _ (algebraMap F (AlgebraicClosure F))
      (rowPolynomial F n signed)) = fun a =>
        algebraMap F (AlgebraicClosure F) (coefficients n (rowPolynomial F n signed) a) := by
    funext a
    exact MonoidAlgebra.coeff_mapRingHom ..
  rw [he]
  rfl

/-- The ordered border size of either row-permutation family is invariant under field
extensions, with the algebraic closure convention on both sides. -/
theorem row_borderSize_extension (n : ℕ) (signed : Bool) :
    borderSize n (rowPolynomial E n signed) = borderSize n (rowPolynomial K n signed) := by
  let : Algebra K (AlgebraicClosure E) :=
    ((algebraMap E (AlgebraicClosure E)).comp (algebraMap K E)).toAlgebra
  let i : AlgebraicClosure K →ₐ[K] AlgebraicClosure E := IsAlgClosed.lift
  let : Algebra (AlgebraicClosure K) (AlgebraicClosure E) := i.toRingHom.toAlgebra
  have hi (s : ℕ) : borderSize n (rowPolynomial E n signed) ≤ s ↔
      borderSize n (rowPolynomial K n signed) ≤ s := by
    rw [rowSize_le_iff, rowSize_le_iff]
    exact rowImage_extend_iff (K := AlgebraicClosure K) (E := AlgebraicClosure E) n s signed
  exact Nat.le_antisymm ((hi _).mpr le_rfl) ((hi _).mp le_rfl)

/-- The ordered border circuit size of the row permanent and row determinant depends
only on the characteristic. In characteristic zero it equals its value over the rationals. -/
theorem row_borderSize_characteristic (F E : Type*) [Field F] [Field E] (q n : ℕ)
    [CharP F q] [CharP E q] (signed : Bool) :
    borderSize n (rowPolynomial F n signed) = borderSize n (rowPolynomial E n signed) := by
  have through (k : Type) [Field k] [Algebra k F] [Algebra k E] :
      borderSize n (rowPolynomial F n signed) = borderSize n (rowPolynomial E n signed) :=
    (row_borderSize_extension (K := k) (E := F) n signed).trans
      (row_borderSize_extension (K := k) (E := E) n signed).symm
  rcases CharP.char_is_prime_or_zero F q with hp | rfl
  · let : Fact q.Prime := ⟨hp⟩
    let := ZMod.algebra F q
    let := ZMod.algebra E q
    exact through (ZMod q)
  · let := CharP.charP_to_charZero F
    let := CharP.charP_to_charZero E
    exact through ℚ

end Ordered

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.ModelExtension
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod

/-!
# Extending scalars in the geometric border model

The equations of the degree-component circuit image extend over an infinite field by
specializing a generic scalar at each scalar label. Conversely, an equation with coefficients
in the larger field restricts to equations over the base by taking linear coordinates of its
coefficients. Consequently the geometric gate bound is invariant under every field extension.
-/

namespace OAI
namespace Computability
namespace BorderVNP

open MvPolynomial

variable {K E σ : Type*} [Field K] [Field E] [Algebra K E]

private theorem specialization {k e a σ : Type*} [Field k] [Field a] {d m : ℕ}
    (g : VPVNP.Circuit (MvPolynomial e k) σ m) (t : MvPolynomial (DegreeMonomial σ d) k)
    (f : MvPolynomial e k →+* a) :
    eval₂ (f.comp C) (coeffVector d (g.mapConstants f).polynomial) t =
      f (eval₂ C (fun j : DegreeMonomial σ d => g.polynomial.coeff j.val) t) := by
  rw [hom_eval₂, VPVNP.Circuit.map_polynomial]
  congr 1

/-- An equation holding on the degree component of every size-bounded circuit over an
infinite base field holds over an arbitrary extension field, at the same gate count. -/
theorem circuitImage_equation_baseChange [Infinite K] {d s : ℕ}
    (t : MvPolynomial (DegreeMonomial σ d) K)
    (ht : ∀ x ∈ circuitImage K σ d s, eval x t = 0) :
    ∀ x ∈ circuitImage E σ d s, eval x (map (algebraMap K E) t) = 0 := by
  rintro _ ⟨m, hm, c, rfl⟩
  let g := c.mapConstants (X : E → MvPolynomial E K)
  let u := eval₂ C (fun j : DegreeMonomial σ d => g.polynomial.coeff j.val) t
  have hu : u = 0 := by
    apply MvPolynomial.funext
    intro a
    rw [map_zero, ← specialization g t (eval a)]
    have ha : (eval a).comp C = RingHom.id K := by ext x; simp
    simpa only [ha, eval₂_id] using ht _ ⟨m, hm, g.mapConstants (eval a), rfl⟩
  let f := (aeval (id : E → E) : MvPolynomial E K →ₐ[K] E).toRingHom
  have hc : g.mapConstants f = c := by
    rw [VPVNP.Circuit.mapConstants_comp]
    apply VPVNP.Circuit.mapConstants_self
    intro x _
    simp [f]
  have hf : f.comp C = algebraMap K E := by ext a; simp [f]
  rw [eval_map, ← hf, ← hc, specialization]
  change f u = 0
  rw [hu, map_zero]

/-- Degree-component border membership over an infinite field descends from the extended
circuit image. This direction extends the equations by specializing generic scalar inputs. -/
theorem geometricApprox_of_baseChange [Infinite K] {d s : ℕ} {p : MvPolynomial σ K}
    (h : geometricApprox d s (map (algebraMap K E) p)) : geometricApprox d s p := by
  intro t ht
  have he := h (map (algebraMap K E) t) (circuitImage_equation_baseChange t ht)
  rw [coeffVector_map, ← map_eval] at he
  exact (algebraMap K E).injective (he.trans (map_zero _).symm)

/-- Ground points have the same degree-component image-closure membership over any extension
of an infinite field. Both the equations and the circuit scalar labels may be extended. -/
theorem geometricApprox_map_iff [Infinite K] (d s : ℕ) (p : MvPolynomial σ K) :
    geometricApprox d s (map (algebraMap K E) p) ↔ geometricApprox d s p := by
  refine ⟨geometricApprox_of_baseChange, fun h => ?_⟩
  unfold geometricApprox
  rw [coeffVector_map]
  apply map_mem_imageClosure _ h
  rintro _ ⟨m, hm, c, rfl⟩
  exact ⟨m, hm, c.mapConstants (algebraMap K E), by rw [c.map_polynomial, coeffVector_map]⟩

/-- For any base field, comparing geometric approximations passes to an embedding of its
algebraic closure into an algebraic closure of the extension. -/
theorem borderApprox_map_iff (d s : ℕ) (p : MvPolynomial σ K) :
    BorderApprox d s (map (algebraMap K E) p) ↔ BorderApprox d s p := by
  let : Algebra K (AlgebraicClosure E) :=
    ((algebraMap E (AlgebraicClosure E)).comp (algebraMap K E)).toAlgebra
  let i : AlgebraicClosure K →ₐ[K] AlgebraicClosure E := IsAlgClosed.lift
  let : Algebra (AlgebraicClosure K) (AlgebraicClosure E) := i.toRingHom.toAlgebra
  have hcomp : (algebraMap (AlgebraicClosure K) (AlgebraicClosure E)).comp
      (algebraMap K (AlgebraicClosure K)) =
      (algebraMap E (AlgebraicClosure E)).comp (algebraMap K E) := by
    ext x
    exact i.commutes x
  simpa only [BorderApprox, map_map, hcomp] using
    (geometricApprox_map_iff (E := AlgebraicClosure E) d s (map (algebraMap K (AlgebraicClosure K)) p))

/-- The geometric border size of a polynomial is invariant under extension of the scalar
field. -/
theorem borderSize_map (d : ℕ) (p : MvPolynomial σ K) :
    borderSize d (map (algebraMap K E) p) = borderSize d p := by
  apply Nat.le_antisymm
  · exact borderSize_le_iff.mpr ((borderApprox_map_iff _ _ _).mpr (borderSize_spec _ _))
  · exact borderSize_le_iff.mpr ((borderApprox_map_iff _ _ _).mp (borderSize_spec _ _))

/-- The geometric border size of an integer polynomial depends on the characteristic
alone. In positive characteristic it is the value over the prime field, and in characteristic
zero it is the value over the rationals. -/
theorem borderSize_intCast_eq {K F σ : Type*} [Field K] [Field F] (q d : ℕ)
    [CharP K q] [CharP F q] (p : MvPolynomial σ ℤ) :
    borderSize d (map (Int.castRingHom K) p) = borderSize d (map (Int.castRingHom F) p) := by
  have through (k : Type) [Field k] [Algebra k K] [Algebra k F] :
      borderSize d (map (Int.castRingHom K) p) = borderSize d (map (Int.castRingHom F) p) := by
    have hK : (algebraMap k K).comp (Int.castRingHom k) = Int.castRingHom K := Subsingleton.elim ..
    have hF : (algebraMap k F).comp (Int.castRingHom k) = Int.castRingHom F := Subsingleton.elim ..
    simpa only [map_map, hK, hF] using (borderSize_map (E := K) d (map (Int.castRingHom k) p)).trans
      (borderSize_map (E := F) d (map (Int.castRingHom k) p)).symm
  rcases CharP.char_is_prime_or_zero K q with hp | rfl
  · let : Fact q.Prime := ⟨hp⟩
    let := ZMod.algebra K q
    let := ZMod.algebra F q
    exact through (ZMod q)
  · let := CharP.charP_to_charZero K
    let := CharP.charP_to_charZero F
    exact through ℚ

end BorderVNP
end Computability
end OAI

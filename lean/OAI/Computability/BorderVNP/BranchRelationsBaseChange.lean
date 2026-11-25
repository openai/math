import OAI.Computability.BorderVNP.BranchChartIndependent
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! # Base change of graph relations

The deformation component initially gives a point satisfying the graph equations
over the constant field. Effective avoidance is performed over the field of rational
functions in the deformation parameter. The two tests agree on that component:
expand an extension-field equation in an independent finite set of coefficient
scalars and test each coefficient polynomial on the rationally parametrized graph.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

variable {K T L I : Type*} [Field K] [Field T] [Field L] [Algebra K T] [Algebra T L]
  [Algebra K L] [IsScalarTower K T L] {m : ℕ}

set_option maxHeartbeats 800000 in
/-- A polynomial over an extension is a finite combination of polynomials over its base
with linearly independent coefficient multipliers. -/
theorem decompose_extension_polynomial (p : MvPolynomial I T) :
    ∃ (n : ℕ) (b : Fin n → T) (P : Fin n → MvPolynomial I K),
      LinearIndependent K b ∧ p = ∑ i, C (b i) * map (algebraMap K T) (P i) := by
  classical
  let c (a : p.support) := p.coeff a.val
  let S := Submodule.span K (Set.range c)
  have : Module.Finite K S := Module.Finite.span_of_finite K (Set.finite_range c)
  let B := Module.finBasis K S
  let v (a : p.support) : S := ⟨c a, Submodule.subset_span ⟨a, rfl⟩⟩
  let r (a : p.support) (i : Fin (Module.finrank K S)) := B.repr (v a) i
  let b (i : Fin (Module.finrank K S)) := S.subtype (B i)
  let P (i : Fin (Module.finrank K S)) := ∑ a : p.support, monomial a.val (r a i)
  have hb : LinearIndependent K b := B.linearIndependent.map' S.subtype (Submodule.ker_subtype _)
  have hcoeff (a : p.support) : ∑ i, b i * algebraMap K T (r a i) = c a := by
    have h := congrArg S.subtype (B.sum_repr (v a))
    have hv : S.subtype (v a) = c a := rfl
    rw [hv] at h
    calc
      _ = ∑ i, r a i • b i := Finset.sum_congr rfl fun i _ => by
        rw [Algebra.smul_def, mul_comm]
      _ = c a := by simpa only [r, b, map_sum, map_smul] using h
  refine ⟨_, b, P, hb, ?_⟩
  simp only [P, map_sum, Finset.mul_sum, map_monomial, C_mul_monomial]
  rw [Finset.sum_comm]
  simp_rw [← map_sum, hcoeff]
  exact p.as_sum.trans (Finset.sum_coe_sort _ _).symm

/-- Equations over the extension field holding on all base points also hold at
any extension-valued point satisfying the base-field vanishing ideal. -/
theorem extend_ground_relations (S : Set (I → K)) (z : I → L)
    (hz : ∀ q : MvPolynomial I K, (∀ x ∈ S, eval x q = 0) → aeval z q = 0)
    (p : MvPolynomial I T) (hp : ∀ x ∈ S, eval (algebraMap K T ∘ x) p = 0) : aeval z p = 0 := by
  obtain ⟨n, b, P, hb, rfl⟩ := decompose_extension_polynomial (K := K) p
  have he (x) (hx : x ∈ S) : ∀ i, eval x (P i) = 0 := by
    apply Fintype.linearIndependent_iff.mp hb
    have h := hp x hx
    simpa only [map_sum, map_mul, eval_C, ← map_eval, Algebra.smul_def, mul_comm] using h
  have map_eval' (q : MvPolynomial I K) : aeval z (map (algebraMap K T) q) = aeval z q := by
    rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq K T L]
    rfl
  simp only [map_sum, map_mul, map_eval', hz _ (fun x hx => he x hx _), mul_zero, Finset.sum_const_zero]

/-- Formal vanishing on the generic rational chart is equivalent to vanishing at
all base-field affine parameters off the common denominator. -/
theorem generic_rational_relation_iff [Infinite K] (den : MvPolynomial (Fin m) K)
    (num : I → MvPolynomial (Fin m) K) (hd : den ≠ 0) (p : MvPolynomial I K) :
    aeval (fun i => algebraMap _ (ParameterField (Fin m) K) (num i) / algebraMap _ _ den) p = 0 ↔
      ∀ z : Fin m → K, eval z den ≠ 0 → eval (fun i => eval z (num i) / eval z den) p = 0 := by
  refine ⟨specialize_rational_relation den num hd p, fun h => ?_⟩
  let F := clearedSubstitution den num p.totalDegree p
  have hF : F * den = 0 := by
    apply MvPolynomial.funext
    intro z
    rw [map_mul, map_zero]
    by_cases he : eval z den = 0
    · rw [he, mul_zero]
    · have hs := eval_clearedSubstitution z (fun i => eval z (num i) / eval z den) den num
          (fun i => div_mul_cancel₀ _ he) p le_rfl
      change eval z F = eval _ p * _ at hs
      rw [hs, h z he, zero_mul, zero_mul]
  have hzero := (mul_eq_zero.mp hF).resolve_right hd
  let inc := algebraMap (MvPolynomial (Fin m) K) (ParameterField (Fin m) K)
  have hd' : inc den ≠ 0 := (map_ne_zero_iff inc (IsFractionRing.injective _ _)).mpr hd
  have h := eval_clearedSubstitution (affineParameter m K) (fun i => inc (num i) / inc den) den num
    (fun i => by rw [eval_affineParameter, eval_affineParameter]; exact div_mul_cancel₀ _ hd') p le_rfl
  change aeval _ F = _ at h
  rw [hzero, map_zero, eval_affineParameter] at h
  exact (mul_eq_zero.mp h.symm).resolve_right (pow_ne_zero _ hd')

/-- An extension-field equation for a rational chart vanishes on a point satisfying
every base-field equation of the same chart. -/
theorem rational_kernel_baseChange [Infinite K] (den : MvPolynomial (Fin m) K)
    (num : I → MvPolynomial (Fin m) K) (hd : den ≠ 0) (z : I → L)
    (hz : ∀ q : MvPolynomial I K, aeval (fun i => algebraMap _ (ParameterField (Fin m) K) (num i) /
      algebraMap _ _ den) q = 0 → aeval z q = 0) (p : MvPolynomial I T)
    (hp : aeval (fun i => algebraMap _ (ParameterField (Fin m) T) (map (algebraMap K T) (num i)) /
      algebraMap _ _ (map (algebraMap K T) den)) p = 0) : aeval z p = 0 := by
  let S := {y : I → K | ∃ x : Fin m → K, eval x den ≠ 0 ∧ y = fun i => eval x (num i) / eval x den}
  apply extend_ground_relations S z
  · intro q hq
    apply hz q
    apply (generic_rational_relation_iff den num hd q).mpr
    intro x hx
    exact hq _ ⟨x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    let inc := algebraMap K T
    have hn := (map_ne_zero_iff (map inc) (map_injective _ inc.injective)).mpr hd
    have hx' : eval (inc ∘ x) (map inc den) ≠ 0 := by
      rw [← map_eval]
      exact (map_ne_zero_iff inc inc.injective).mpr hx
    have h := specialize_rational_relation (map inc den) (fun i => map inc (num i)) hn p hp (inc ∘ x) hx'
    have e : (fun i => eval (inc ∘ x) (map inc (num i)) / eval (inc ∘ x) (map inc den)) =
        inc ∘ (fun i => eval x (num i) / eval x den) := by
      funext i
      rw [← map_eval, ← map_eval, ← map_div₀]
      rfl
    rw [e] at h
    exact h

end Branch

end BorderVNP
end Computability
end OAI

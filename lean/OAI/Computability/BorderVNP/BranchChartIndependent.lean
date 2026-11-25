import OAI.Computability.BorderVNP.BranchChart
import OAI.Computability.BorderVNP.BranchGraphBadLocus
import Mathlib.Algebra.MvPolynomial.Funext

/-! # The independent variables of a projective graph chart

The parameter ratios on the chart indexed by `k` contain one redundant coordinate,
equal to one. Replace the `k`th affine coordinate by the zeroth ratio, giving exactly
`h` independent coordinates. Their generic substitution preserves every nonzero
polynomial, which lets the Jacobian equation be used on the actual graph.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

variable {m : ℕ} {K I : Type*} [Field K]

/-- Order the nonconstant coordinates on the chart where homogeneous coordinate `k` is one. -/
def chartIndex (k : Option (Fin m)) (j : Fin m) : Option (Fin m) :=
  if k = some j then none else some j

/-- Evaluation of any rational relation at a point off its common denominator. -/
theorem specialize_rational_relation (den : MvPolynomial (Fin m) K)
    (num : I → MvPolynomial (Fin m) K) (hd : den ≠ 0) (p : MvPolynomial I K)
    (hp : aeval (fun i => algebraMap _ (ParameterField (Fin m) K) (num i) /
      algebraMap _ _ den) p = 0) (z : Fin m → K) (hz : eval z den ≠ 0) :
    eval (fun i => eval z (num i) / eval z den) p = 0 := by
  let inc := algebraMap (MvPolynomial (Fin m) K) (ParameterField (Fin m) K)
  let n := p.totalDegree
  let F := clearedSubstitution den num n p
  have hinc := IsFractionRing.injective (MvPolynomial (Fin m) K) (ParameterField (Fin m) K)
  have hden : inc den ≠ 0 := (map_ne_zero_iff inc hinc).mpr hd
  have hF : F = 0 := by
    apply hinc
    change inc F = inc 0
    rw [map_zero, ← eval_affineParameter]
    rw [eval_clearedSubstitution (affineParameter m K) (fun i => inc (num i) / inc den) den num
      (fun i => by rw [eval_affineParameter, eval_affineParameter]; exact div_mul_cancel₀ _ hden) p le_rfl,
      hp, zero_mul]
  have he := eval_clearedSubstitution z (fun i => eval z (num i) / eval z den) den num
    (fun i => div_mul_cancel₀ _ hz) p le_rfl
  change eval z F = eval _ p * (eval z den)^n at he
  rw [hF, map_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_right (pow_ne_zero _ hz)

/-- The affine chart coordinates preserve formal polynomial nonvanishing under
the generic parameter substitution. -/
theorem generic_chart_nonzero [Infinite K] (k : Option (Fin m))
    (p : MvPolynomial (Fin m) K) (hp : p ≠ 0) :
    aeval (fun j => homogeneousParameters (Fin m) K (chartIndex k j) /
      homogeneousParameters (Fin m) K k) p ≠ 0 := by
  cases k with
  | none =>
    simp only [chartIndex, reduceCtorEq, ite_false, homogeneousParameters, Option.elim_some,
      Option.elim_none, div_one]
    change aeval (affineParameter m K) p ≠ 0
    rw [eval_affineParameter]
    exact (map_ne_zero_iff (algebraMap _ (ParameterField (Fin m) K)) (IsFractionRing.injective _ _)).mpr hp
  | some k =>
    have hpoint : ∃ z : Fin m → K, eval z (p * X k) ≠ 0 := by
      by_contra! h
      exact mul_ne_zero hp (X_ne_zero k) (MvPolynomial.funext fun z => by simpa using h z)
    obtain ⟨z, hz⟩ := hpoint
    rw [map_mul, eval_X, mul_ne_zero_iff] at hz
    let num (j : Fin m) : MvPolynomial (Fin m) K := if k = j then 1 else X j
    let inc := algebraMap (MvPolynomial (Fin m) K) (ParameterField (Fin m) K)
    have hnum (j) : inc (num j) = homogeneousParameters (Fin m) K (chartIndex (some k) j) := by
      by_cases hj : k = j <;> simp [inc, num, chartIndex, homogeneousParameters, hj]
    intro he
    have he' : aeval (fun j => inc (num j) / inc (X k)) p = 0 := by
      simp_rw [hnum]
      exact he
    have hden : eval (chart k z) (X k) ≠ 0 := by simp [chart, hz.2]
    have h := specialize_rational_relation (X k) num (X_ne_zero k) p he' (chart k z) hden
    have eq (j) : eval (chart k z) (num j) / eval (chart k z) (X k) = chart k (chart k z) j := by
      by_cases hj : k = j
      · subst j
        simp [num, chart]
      · simp [num, chart, hj, Ne.symm hj]
    simp_rw [eq] at h
    rw [chart_involutive k z hz.2] at h
    exact hz.1 h

/-- A nonzero exceptional polynomial in the independent chart coordinates is
nonzero in the coordinate algebra of the whole projective graph. -/
theorem graphChart_rename_ne_zero [Infinite K] (Y : I → MvPolynomial (Fin m) K)
    (k : Option (Fin m)) (p : MvPolynomial (Fin m) K) (hp : p ≠ 0) :
    graphChartMap Y k (rename (Sum.inl ∘ chartIndex k) p) ≠ 0 := by
  rw [← graphChartAlgHom_toRingHom]
  change aeval (graphValues Y k) (rename (Sum.inl ∘ chartIndex k) p) ≠ 0
  rw [aeval_rename]
  exact generic_chart_nonzero k p hp

end Branch

end BorderVNP
end Computability
end OAI

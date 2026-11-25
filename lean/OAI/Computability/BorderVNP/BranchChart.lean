import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

/-!
# Parameter charts in the curve construction

On the intersection of the standard chart `(1 : X)` with the chart whose
denominator is `Xₖ`, the coordinate change interchanges the homogeneous
positions `0` and `k`. The same rule gives its inverse, and its differential
is invertible in every characteristic.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

variable {K ι : Type*} [Field K] [DecidableEq ι]

/-- Chart coordinates obtained by moving the nonzero coordinate `x k` to the front. -/
def chart (k : ι) (x : ι → K) : ι → K :=
  fun i => (if i = k then 1 else x i) / x k

/-- The projective chart change is its own inverse on the overlap. -/
theorem chart_involutive (k : ι) (x : ι → K) (hx : x k ≠ 0) :
    chart k (chart k x) = x := by
  funext i
  by_cases hik : i = k
  · subst i
    simp [chart]
  · simp [chart, hik, hx]

/-- The differential of the chart change, acting on a vector of coordinate derivatives. -/
def chartTangent (k : ι) (x w : ι → K) : ι → K :=
  fun i => ((if i = k then 0 else w i) - chart k x i * w k) / x k

/-- Differentiation in any extension field gives the stated chart differential. -/
theorem derivation_chart {R : Type*} [CommRing R] [Algebra R K] (D : Derivation R K K)
    (k : ι) (x : ι → K) :
    (fun i => D (chart k x i)) = chartTangent k x (fun i => D (x i)) := by
  funext i
  by_cases hx : x k = 0
  · simp [chart, chartTangent, hx]
  by_cases hik : i = k
  · subst i
    simp [chart, chartTangent, D.leibniz_inv]
    ring
  · simp only [chart, chartTangent, hik, ite_false, D.leibniz_div, smul_eq_mul]
    field_simp

/-- The two chart differentials are inverse on the overlap, including in characteristic two. -/
theorem chartTangent_inverse (k : ι) (x w : ι → K) (hx : x k ≠ 0) :
    chartTangent k (chart k x) (chartTangent k x w) = w := by
  funext i
  by_cases hik : i = k
  · subst i
    simp [chartTangent, chart]
    field_simp
  · simp [chartTangent, chart, hik]
    field_simp
    ring

/-- The coordinate change in the proof of Proposition 9.2 has a bijective differential. -/
theorem chartTangent_bijective (k : ι) (x : ι → K) (hx : x k ≠ 0) :
    Function.Bijective (chartTangent k x) := by
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨chartTangent k (chart k x), fun w => chartTangent_inverse k x w hx, ?_⟩
  intro w
  have hchart : chart k x k ≠ 0 := by simp [chart, hx]
  simpa only [chart_involutive k x hx] using chartTangent_inverse k (chart k x) w hchart

end Branch

end BorderVNP
end Computability
end OAI

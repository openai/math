import OAI.Hierarchy.ProbeScore
import Mathlib.Tactic

namespace OAI
/-! # The actual payload-and-altimeter score and its purchase trigger -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators
noncomputable section

/-- One payload per source record, plus one signed altimeter per tile and direction. -/
abbrev Commodity (P : Type*) (N k : ℕ) := P ⊕ ((P × Fin N) × (Fin k × Bool))

variable {P : Type*} [Fintype P] {N k : ℕ}

def bonus (B : ℝ) : Commodity P N k → ℝ
  | .inl _ => 0
  | .inr _ => B

def readings (M : ℝ) (x : Commodity P N k → ℝ) :=
  ∑ t : P × Fin N, ∑ j : Fin k × Bool, (rise M (x (.inr (t,j))))^2

/-- The implemented separable potential on the real physical inventory has exactly
one quadratic base term per commodity and one marked reading per directed axis. -/
theorem score_actual (a M B : ℝ) (x : Commodity P N k → ℝ) :
    score a M (bonus B) x = a*(∑ i, (x i)^2) + B*readings M x := by
  unfold score rowScore readings
  rw [Finset.sum_add_distrib,←Finset.mul_sum,Fintype.sum_sum_type]
  simp [bonus,Fintype.sum_prod_type,Finset.mul_sum,mul_add]

/-- The truncated reciprocal time envelope used by the outer cooling schedule. -/
def envelope (W r s : ℝ) := W⁻¹^2 * min (1/s) (1/r)

/-- Near or above the truncation time, any excess of the score itself forces the
normalized squared reading statistic above the marking threshold. -/
theorem score_triggers {s r W base E f : ℝ} (hs : 0 < s) (s1 : s ≤ 1) (hr : 0 < r)
    (above : r ≤ s) (wide : 2*W⁻¹^4 ≤ W⁻¹^2)
    (small : base ≤ W⁻¹^4) (expand : f=base+W⁻¹^4*E)
    (high : envelope W r s < f) : 1 < s*E := by
  have rate := one_div_le_one_div_of_le hr above
  rw [envelope,min_eq_left rate,mul_one_div] at high
  have paid := (div_lt_iff₀ hs).mp high
  by_contra! low
  have e := mul_le_mul_of_nonneg_left low (show 0 ≤ W⁻¹^4 by positivity)
  have c := mul_le_mul_of_nonneg_left small hs.le
  have c' := mul_le_mul_of_nonneg_right s1 (show 0 ≤ W⁻¹^4 by positivity)
  nlinarith only [e,c,c',wide,paid,congrArg (fun q => q*s) expand]

/-- Below the cutoff every altimeter's positive part is at most one, so a box
score with that many coordinates can never trigger a purchase by itself. -/
theorem no_small_time_excess {s r W base E J f : ℝ} (hs : 0 < s) (hr : 0 < r)
    (too_early : s ≤ r) (small : base ≤ W⁻¹^4) (cap : E ≤ J)
    (wide : W⁻¹^4*(1+J)*r ≤ W⁻¹^2) (expand : f=base+W⁻¹^4*E) :
    f ≤ envelope W r s := by
  have rate := one_div_le_one_div_of_le hs too_early
  rw [envelope,min_eq_right rate,mul_one_div,le_div_iff₀ hr]
  have e := mul_le_mul_of_nonneg_left cap (show 0 ≤ W⁻¹^4 by positivity)
  have q : f ≤ W⁻¹^4*(1+J) := by rw [expand]; nlinarith only [small,e]
  exact (mul_le_mul_of_nonneg_right q hr.le).trans wide

end
end Hierarchy.AdaptiveProbe

end OAI

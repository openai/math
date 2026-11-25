import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI
/-! # Choice of a dyadic probe scale with all required capacity margins -/

namespace Hierarchy.AdaptiveProbe
open Filter Topology
noncomputable section

def dyadicScale (W : ℕ) : ℝ := (1/2:ℝ)^W

theorem dyadic_price_decay (m : ℕ) {a : ℝ} (positive : 0 < a) :
    Tendsto (fun W : ℕ => (W:ℝ)^m*(dyadicScale W)^a) atTop (𝓝 0) := by
  have base : 0≤(1/2:ℝ)^a := Real.rpow_nonneg (by norm_num) _
  have small : (1/2:ℝ)^a<1 := Real.rpow_lt_one (by norm_num) (by norm_num) positive
  simpa only [dyadicScale,←Real.rpow_pow_comm (by norm_num : 0≤(1/2:ℝ))] using
    tendsto_pow_const_mul_const_pow_of_abs_lt_one m (by rwa [abs_of_nonneg base])

/-- The constants C and coefficient K absorb the stage count and factors 64kΛ.
The same W works for every stage count satisfying N t ≤ C and every h thereafter. -/
theorem affordable_scale {p σ C K τ : ℝ} (hp : 1 < p) (hσ : 0<σ)
    (_hC : 0 < C) (hK : 0 < K) (hτ : 0<τ) :
    ∀ᶠ W : ℕ in atTop, let t := dyadicScale W
      K*t^σ≤1 ∧ ∀ N : ℝ, 0 ≤ N → N*t ≤ C →
        K*(W:ℝ)^4*N*t^p≤1 ∧ N*t^2≤τ := by
  have fee := (dyadic_price_decay 4 (sub_pos.mpr hp)).const_mul (K*C)
  have unit := (dyadic_price_decay 0 hσ).const_mul K
  have tiles := (dyadic_price_decay 0 (show 0<(1:ℝ) by norm_num)).const_mul C
  simp only [mul_zero,pow_zero,one_mul,Real.rpow_one] at fee unit tiles
  filter_upwards [fee.eventually_lt_const zero_lt_one,unit.eventually_lt_const zero_lt_one,
    tiles.eventually_lt_const hτ] with W paid ok compact
  let t := dyadicScale W
  have ht : 0 < t := by dsimp [t,dyadicScale]; positivity
  have split : t^p=t*t^(p-1) := by
    calc
      t^p = t^(1+(p-1)) := by congr 1; ring
      _ = t*t^(p-1) := by rw [Real.rpow_add ht,Real.rpow_one]
  refine ⟨ok.le,fun N _ stages => ⟨?_,?_⟩⟩
  · change K*(W:ℝ)^4*N*t^p≤1
    rw [split]
    have factor : 0 ≤ K*(W:ℝ)^4*t^(p-1) := by positivity
    have bulk := mul_le_mul_of_nonneg_right stages factor
    change K*C*((W:ℝ)^4*t^(p-1))<1 at paid
    nlinarith only [paid,bulk]
  · change N*t^2≤τ
    nlinarith only [mul_le_mul_of_nonneg_right stages ht.le,compact.le]

end
end Hierarchy.AdaptiveProbe

end OAI

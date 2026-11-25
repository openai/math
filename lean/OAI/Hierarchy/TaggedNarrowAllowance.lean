import OAI.Hierarchy.TaggedWidthInduction

namespace OAI
/-! # Uniform cost margin at the initial width exponent -/

noncomputable section
namespace Hierarchy.Tagged
open Filter Real

/-- The margin between the available rate and the trial function absorbs
every fixed prefactor on a uniform positive-width strip. -/
theorem narrow_allowance {s r : ℝ} {u : ℝ → ℝ} (hu : TaggedWidthProfile.Admissible s u)
    (margin : r < u 1) : ∃ κ : ℝ, 0 < κ ∧ ∀ A : ℝ, ∀ᶠ h : ℕ in atTop,
      ∀ w : ℕ, h ≤ w → logb h w ≤ 1+κ →
        (w:ℝ) ≤ (h:ℝ)^(1+κ) ∧ A*work h w r ≤ unitWork u h w := by
  let κ := (u 1-r)/3
  have pos : 0 < κ := by dsimp [κ]; linarith
  refine ⟨κ,pos,fun A => ?_⟩
  have grows := ((tendsto_rpow_atTop pos).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop A
  filter_upwards [grows,eventually_ge_atTop (2:ℕ)] with h enough hh
  intro w wide narrow
  have hp : (1:ℝ) < h := by exact_mod_cast (show 1 < h by omega)
  have wid : (h:ℝ) ≤ w := by exact_mod_cast wide
  have wp := (zero_lt_one.trans hp).trans_le wid
  let a := logb h w
  have one : 1 ≤ a := (le_logb_iff_rpow_le hp wp).mpr (by simpa using wid)
  have lower := (hu.uniform_margins (1+κ)).2 a one
  have headroom : r+κ ≤ u a := calc
    _ ≤ u 1-κ := by dsimp [κ]; linarith
    _ ≤ u a := by
      change a ≤ 1+κ at narrow
      linarith
  refine ⟨(logb_le_iff_le_rpow hp wp).mp narrow,?_⟩
  have scale : A*(h:ℝ)^r ≤ (h:ℝ)^u a := calc
    _ ≤ (h:ℝ)^κ*(h:ℝ)^r := mul_le_mul_of_nonneg_right enough (by positivity)
    _ = (h:ℝ)^(r+κ) := by rw [Real.rpow_add (zero_lt_one.trans hp)]; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hp.le headroom
  unfold unitWork work
  calc
    _ = ((2:ℝ)^h*w)*(A*(h:ℝ)^r) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left scale (by positivity)

end Hierarchy.Tagged

end
end OAI

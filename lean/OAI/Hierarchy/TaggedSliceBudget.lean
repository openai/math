import OAI.Hierarchy.TaggedGapScale
import OAI.Hierarchy.TaggedWidthSlices

namespace OAI
/-! # Gap and size budgets for products of shared-tag slices -/

noncomputable section
namespace Hierarchy.Tagged.Slices
open Filter

/-- The loss in a polynomial number of shared-tag calls is absorbed by any
strict increase of the quadratic logarithm coefficient. -/
theorem eventual_gap_after_slices {C D M : ℝ} (hC : 0 ≤ C) (lt : C < D) (hM : 0 ≤ M) (k : ℕ) :
    ∀ᶠ h : ℕ in atTop, ∀ m : ℕ, (m : ℝ) ≤ (h:ℝ)^M → gap D h ≤ gap C h-2*(k:ℝ)*(m:ℝ) := by
  filter_upwards [GapScale.eventual_taller_polynomial hC lt (b:=0) le_rfl 2,
    GapScale.eventual_polynomial D (2*(k:ℝ)) M hM] with h big offset
  intro m hm
  have half := big h le_rfl
  simp only [Real.rpow_zero, mul_one] at half
  have base : 0 ≤ (h:ℝ) := Nat.cast_nonneg _
  have poly : (m:ℝ) ≤ (2*(h:ℝ))^M := hm.trans (Real.rpow_le_rpow base (by linarith) hM)
  have loss := (mul_le_mul_of_nonneg_left poly (by positivity : 0 ≤ 2*(k:ℝ))).trans offset
  linarith

/-- Ceiling division wastes less than one full slice. Across a wider
payload, paying the full capacity price of every slice costs at most twice
the allowance for the actual columns. -/
theorem work_cover {h w V : ℕ} {A r : ℝ} (hA : 0 ≤ A) (wide : V ≤ w) :
    (TaggedWidthSlices.count w V:ℝ)*(A*work h V r) ≤ (2*A)*work h w r := by
  let m := TaggedWidthSlices.count w V
  have fill : m * V ≤ w+V-1 := Nat.div_mul_le_self _ _
  have two : (m:ℝ)*(V:ℝ) ≤ 2*(w:ℝ) := by exact_mod_cast (show m*V ≤ 2*w by omega)
  calc
    _ = (m*V:ℝ)*(A*(2:ℝ)^h*(h:ℝ)^r) := by unfold work; ring
    _ ≤ (2*w:ℝ)*(A*(2:ℝ)^h*(h:ℝ)^r) := mul_le_mul_of_nonneg_right two (by positivity)
    _ = _ := by unfold work; ring

end Hierarchy.Tagged.Slices

end
end OAI

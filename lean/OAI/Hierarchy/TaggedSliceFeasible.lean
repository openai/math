import OAI.Hierarchy.TaggedSlices
import OAI.Hierarchy.TaggedPinning
import OAI.Hierarchy.TaggedApproximation
import OAI.Hierarchy.TaggedSliceBudget

namespace OAI
/-! # Uniform width changes for feasible tagged approximations -/

noncomputable section
namespace Hierarchy.Tagged.Slices
open Filter Catalyst
open scoped BigOperators Classical

variable {F : Type*} [Field F] {k h w C : ℕ}

/-- Use copies of a single format to serve a wider test. Matching zero
padding on the two ends supplies the unused columns of each balanced slice. -/
theorem from_one (hw : 0 < w) (hC : 0 < C) (X : Approximation F k (pins h C))
    {G : ℝ} (price : X.Gap (coeff F h C) G) :
    ∃ Y : Approximation F k (pins h w), Y.size ≤ TaggedWidthSlices.count w C * X.size ∧
      Y.Gap (coeff F h w) (G-2*(k:ℝ)*(TaggedWidthSlices.count w C)) := by
  choose Z _ size prices using fun i : Fin (TaggedWidthSlices.count w C) =>
    narrower (TaggedWidthSlices.width_le hC i) X price
  obtain ⟨Y,bill,hgap⟩ := balanced hw hC Z
  refine ⟨Y,bill.trans ?_,hgap G prices⟩
  simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => size i)

/-- The baseline may be any feasible exponent. At each larger polynomially
bounded width, the size bill is at most twice the baseline rate allowance. -/
theorem eventually_from_feasible {k : ℕ} {a r : ℝ} (base : Feasible F k a r) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧ ∀ D M : ℝ, C < D → 0 ≤ M →
      ∀ᶠ h : ℕ in atTop, ∀ w : ℕ, width h a ≤ w → (w:ℝ) ≤ (h:ℝ)^M →
        ∃ Y : Approximation F k (pins h w),
          (Y.size:ℝ) ≤ A*work h w r ∧ Y.Gap (coeff F h w) (gap D h) := by
  obtain ⟨A,C,hA,hC,feasible⟩ := base
  refine ⟨2*A,C,by positivity,hC,fun D M hD hM => ?_⟩
  filter_upwards [feasible,eventual_gap_after_slices hC.le hD hM k,eventually_ge_atTop (1:ℕ)]
    with h ok gapBound hh
  intro w wide cap
  obtain ⟨X,size,price⟩ := ok
  let V := width h a
  let m := TaggedWidthSlices.count w V
  have hp : 0 < (h:ℝ) := by exact_mod_cast hh
  have pos : 0 < V := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hp _)
  have few : m ≤ w := TaggedWidthSlices.count_le pos (Nat.le_mul_of_pos_right w pos)
  obtain ⟨Y,bill,score⟩ := from_one (pos.trans_le wide) pos X price
  refine ⟨Y,?_,Approximation.Gap.mono _ score (gapBound m ((by exact_mod_cast few :
    (m:ℝ)≤w).trans cap))⟩
  calc
    (Y.size:ℝ) ≤ (m:ℝ)*(X.size:ℝ) := by exact_mod_cast bill
    _ ≤ (m:ℝ)*(A*work h V r) := mul_le_mul_of_nonneg_left size (Nat.cast_nonneg _)
    _ ≤ _ := work_cover hA.le wide

/-- Constant factors in the payload width can be chosen after the baseline
estimate. A single size constant and gap coefficient cover the whole band. -/
theorem eventually_constant_width {k : ℕ} {a r : ℝ} (base : Feasible F k a r)
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧ ∀ᶠ h : ℕ in atTop, ∀ w : ℕ,
      (width h a:ℝ) ≤ B*w → (w:ℝ) ≤ B*width h a →
      ∃ Y : Approximation F k (pins h w), (Y.size:ℝ) ≤ A*work h w r ∧
        Y.Gap (coeff F h w) (gap D h) := by
  obtain ⟨A,C,hA,hC,baseline⟩ := base
  let b := ⌈B⌉₊
  have hb : B ≤ (b:ℝ) := Nat.le_ceil _
  have pos : 0 < B := zero_lt_one.trans_le hB
  have bp : 0 < (b:ℝ) := pos.trans_le hb
  refine ⟨(b:ℝ)*A*B,C+1,by positivity,by linarith,?_⟩
  filter_upwards [baseline,eventual_gap_after_slices hC.le (show C<C+1 by linarith)
    (show (0:ℝ) ≤ 1 by norm_num) k,eventually_ge_atTop (max 1 b)] with h ok discount hh
  intro w vmin vmax
  let V := width h a
  have hp : 0 < (h:ℝ) := by exact_mod_cast (show 0<h by omega)
  have hv : 0 < V := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hp _)
  have hw : 0 < w := by
    by_contra z
    have ze : w = 0 := by omega
    have le : (V:ℝ) ≤ 0 := by simpa [ze] using vmin
    exact (not_le_of_gt (by exact_mod_cast hv : (0:ℝ) < V)) le
  have upper : w ≤ b*V := by
    exact_mod_cast vmax.trans (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _))
  have few := TaggedWidthSlices.count_le hv upper
  obtain ⟨X,size,price⟩ := ok
  obtain ⟨Y,bill,score⟩ := from_one hw hv X price
  refine ⟨Y,?_,Approximation.Gap.mono _ score (discount _ ?_)⟩
  · calc
      (Y.size:ℝ) ≤ (b:ℝ)*(X.size:ℝ) := by exact_mod_cast bill.trans (Nat.mul_le_mul_right _ few)
      _ ≤ (b:ℝ)*(A*work h V r) := mul_le_mul_of_nonneg_left size (Nat.cast_nonneg _)
      _ = (V:ℝ)*(b*A*(2:ℝ)^h*(h:ℝ)^r) := by unfold work; ring
      _ ≤ (B*w)*(b*A*(2:ℝ)^h*(h:ℝ)^r) :=
        mul_le_mul_of_nonneg_right vmin (by positivity)
      _ = _ := by unfold work; ring
  · rw [Real.rpow_one]
    exact_mod_cast (few.trans (by omega : b ≤ h))

end Hierarchy.Tagged.Slices

end
end OAI

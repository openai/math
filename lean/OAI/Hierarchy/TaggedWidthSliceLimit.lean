import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

namespace OAI
/-! # Width exponents of integer slices in the plateau -/

namespace Hierarchy.TaggedWidthProfile

open Filter Real
open scoped Topology

/-- If a balanced slice has width between half the capacity (up to a unit)
and capacity, its width exponent eventually lies in the chosen plateau. -/
theorem eventually_slice_formats (start cap : ℝ) (hs : 0 ≤ start) (gap : start < cap) :
    ∀ᶠ h : ℝ in atTop, ∀ v : ℕ, v ≤ ⌊h ^ cap⌋₊ → ⌊h ^ cap⌋₊ ≤ 2 * (v + 1) →
      start ≤ log (v : ℝ) / log h ∧ log (v : ℝ) / log h ≤ cap := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop (sub_pos.mpr gap)).eventually_gt_atTop 6] with h hh six
  intro v vmax vmin
  have hp := zero_lt_one.trans hh
  have base := Real.one_le_rpow hh.le hs
  have prod : h ^ start * h ^ (cap - start) = h ^ cap := by
    rw [← Real.rpow_add hp]
    ring_nf
  have lower := mul_lt_mul_of_pos_left six (Real.rpow_pos_of_pos hp start)
  rw [prod] at lower
  have floor := Nat.lt_floor_add_one (h ^ cap)
  have near : (⌊h ^ cap⌋₊ : ℝ) ≤ 2 * ((v : ℝ) + 1) := by exact_mod_cast vmin
  have l : h ^ start ≤ (v : ℝ) := by linarith
  have r : (v : ℝ) ≤ h ^ cap :=
    (Nat.cast_le.mpr vmax).trans (Nat.floor_le (Real.rpow_pos_of_pos hp _).le)
  have vp := (Real.rpow_pos_of_pos hp start).trans_le l
  have lh := Real.log_le_log (Real.rpow_pos_of_pos hp start) l
  have rh := Real.log_le_log vp r
  rw [Real.log_rpow hp] at lh rh
  exact ⟨(le_div_iff₀ (Real.log_pos hh)).mpr lh, (div_le_iff₀ (Real.log_pos hh)).mpr rh⟩

/-- A type with fixed positive height ratio and payload fraction Y has a
bounded number of slices for every parent width, after rounding the child
width upwards and its admissible capacity downwards. -/
theorem eventually_slice_count {ι : Type*} {l : Filter ι} {cap T Y : ℝ}
    (hc : 0 < cap) (ht : 0 < T) (hy : 0 ≤ Y) (h hp : ι → ℝ)
    (large : Tendsto hp l atTop) (ratio : Tendsto (fun i => hp i / h i) l (𝓝 T))
    (positive : ∀ᶠ i in l, 0 < h i) :
    ∃ B : ℕ, ∀ᶠ i in l, ∀ w : ℝ, w ≤ h i ^ cap →
      ⌈Y * w⌉₊ ≤ ⌊hp i ^ cap⌋₊ * B := by
  let K := 2 / T
  have hk : 0 < K := div_pos (by norm_num) ht
  let B := ⌈2 * (Y * K ^ cap)⌉₊
  refine ⟨B, ?_⟩
  have scale := (tendsto_rpow_atTop hc).comp large
  filter_upwards [positive, large.eventually_gt_atTop 0, scale.eventually_gt_atTop 2,
    ratio.eventually (eventually_gt_nhds (show T / 2 < T by linarith))] with i hh hp' twice near
  change 2 < hp i ^ cap at twice
  intro w hw
  have small : h i ≤ hp i * K := by
    dsimp [K]
    rw [mul_div_assoc', le_div_iff₀ ht]
    have e := (lt_div_iff₀ hh).mp near
    linarith
  have power := Real.rpow_le_rpow hh.le small hc.le
  rw [Real.mul_rpow hp'.le hk.le] at power
  have floor : hp i ^ cap ≤ 2 * (⌊hp i ^ cap⌋₊ : ℝ) := by
    linarith [Nat.lt_floor_add_one (hp i ^ cap)]
  have enough : 2 * (Y * K ^ cap) ≤ (B : ℝ) := Nat.le_ceil _
  apply Nat.ceil_le.mpr
  rw [Nat.cast_mul]
  calc
    Y * w ≤ Y * (hp i ^ cap * K ^ cap) := mul_le_mul_of_nonneg_left (hw.trans power) hy
    _ = hp i ^ cap * (Y * K ^ cap) := by ring
    _ ≤ (2 * (⌊hp i ^ cap⌋₊ : ℝ)) * (Y * K ^ cap) :=
      mul_le_mul_of_nonneg_right floor (mul_nonneg hy (Real.rpow_pos_of_pos hk _).le)
    _ = (⌊hp i ^ cap⌋₊ : ℝ) * (2 * (Y * K ^ cap)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left enough (Nat.cast_nonneg _)

end Hierarchy.TaggedWidthProfile

end OAI

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

/-! # The two limits in the exterior split tree

At depth `a`, the tree has `2 ^ a` leaves. The resulting factor costs
`a * log 2 / log q` in the exponent and vanishes as the wire dimension
`q` grows. The remaining width error vanishes as the split depth grows.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Real
open scoped Topology

/-- Finite logarithmic bound for a wire whose normalized leaves have common
exponent bound `b` at depth `a`. -/
theorem relocation_depth_log_bound {q d b : ℝ} (hq : 1 < q) (a : ℕ)
    (h : q ^ d ≤ (2 : ℝ) ^ a * q ^ b) :
    d ≤ b + a * log 2 / log q := by
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hq₀ _) h
  rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hq₀ _).ne',
    Real.log_pow, Real.log_rpow hq₀, Real.log_rpow hq₀] at hl
  have : d - b ≤ a * log 2 / log q :=
    (le_div_iff₀ (Real.log_pos hq)).2 (by linarith only [hl])
  linarith only [this]

/-- For each fixed split depth the leaf-count factor disappears as the
integer wire dimension grows. The error may depend on the depth. -/
theorem relocation_fixed_depth_bound {d b : ℝ} (a : ℕ) {err : ℕ → ℝ}
    (herr : Tendsto err atTop (𝓝 0))
    (h : ∀ᶠ q : ℕ in atTop, (q : ℝ) ^ d ≤ (2 : ℝ) ^ a * (q : ℝ) ^ (b + err q)) :
    d ≤ b := by
  have hlog : Tendsto (fun q : ℕ ↦ log (q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcount : Tendsto (fun q : ℕ ↦ a * log 2 / log (q : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hlim : Tendsto (fun q : ℕ ↦ b + err q + a * log 2 / log (q : ℝ)) atTop (𝓝 b) := by
    simpa using (herr.const_add b).add hcount
  apply ge_of_tendsto hlim
  filter_upwards [h, eventually_gt_atTop 1] with q hq hq₁
  exact relocation_depth_log_bound (by exact_mod_cast hq₁) a hq

/-- For a fixed finite set of leaves, their individual exponent errors can
be replaced by one vanishing error. The sum of the normalized values then
has a prefactor equal to the number of leaves. -/
theorem relocation_leaf_sum_bound {ι : Type*} [Fintype ι] (v : ι → ℕ → ℝ) {b : ℝ}
    (h : ∀ i, ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ q : ℕ in atTop, v i q ≤ (q : ℝ) ^ (b + e q)) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ q : ℕ in atTop, ∑ i, v i q ≤ Fintype.card ι * (q : ℝ) ^ (b + e q) := by
  classical
  choose err herr hleaf using h
  refine ⟨fun q ↦ ∑ i, |err i q|, ?_, ?_⟩
  · simpa using tendsto_finsetSum Finset.univ (fun i _ ↦ (herr i).abs)
  filter_upwards [eventually_all.mpr hleaf, eventually_ge_atTop 1] with q hq hq₁
  calc
    _ ≤ ∑ _i : ι, (q : ℝ) ^ (b + ∑ j, |err j q|) := by
      apply Finset.sum_le_sum
      intro i _
      have hei : err i q ≤ ∑ j, |err j q| := (le_abs_self _).trans
        (Finset.single_le_sum (fun j _ ↦ abs_nonneg (err j q)) (Finset.mem_univ i))
      exact (hq i).trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq₁)
        (add_le_add_right hei b))
    _ = _ := by simp

/-- Letting the depth grow removes the width loss from repeated halving. -/
theorem relocation_width_limit {d B w : ℝ}
    (h : ∀ a : ℕ, d ≤ B + w / (2 : ℝ) ^ a) : d ≤ B := by
  have hw : Tendsto (fun a : ℕ ↦ w / (2 : ℝ) ^ a) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  exact ge_of_tendsto' (by simpa using hw.const_add B) h

/-- A path with error at most `ε` per split loses at most `a * ε`.
This bound at every positive tolerance and depth gives the exact inequality. -/
theorem relocation_depth_slack_limit {d B w : ℝ}
    (h : ∀ (a : ℕ) (ε : ℝ), 0 < ε → d ≤ B + w / (2 : ℝ) ^ a + a * ε) : d ≤ B := by
  apply relocation_width_limit (w := w)
  intro a
  have he : Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply ge_of_tendsto' (by simpa using (he.const_mul (a : ℝ)).const_add (B + w / (2 : ℝ) ^ a))
  intro n
  exact h a _ (by positivity)

/-- The root exponent is bounded by the coupling cost if the finite split
bounds hold at every depth, with a vanishing dimension error for each depth. -/
theorem relocation_iterated_depth_bound {d B w : ℝ}
    (h : ∀ a : ℕ, ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ q : ℕ in atTop, (q : ℝ) ^ d ≤
        (2 : ℝ) ^ a * (q : ℝ) ^ (B + w / (2 : ℝ) ^ a + err q)) :
    d ≤ B := by
  apply relocation_width_limit (w := w)
  intro a
  obtain ⟨err, herr, hq⟩ := h a
  exact relocation_fixed_depth_bound a herr hq

end SpectralBooks
end LinearAlgebra
end OAI

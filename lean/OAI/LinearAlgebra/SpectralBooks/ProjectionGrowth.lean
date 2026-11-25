import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # Transfer of a border-size exponent through polynomial padding

These are the numerical estimates in the projection to the universal polynomial
at the end of the characteristic-wise alternative. With padding `N ≥ A * n ^ b`,
a quadratic homogeneous-specialization overhead preserves every positive
exponent below `ε / b`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter

/-- The source size chosen by inverting the real polynomial padding bound and rounding down. -/
noncomputable def paddingIndex {A b : ℝ} (N : ℕ) : ℕ := ⌊((N : ℝ) / A) ^ (1 / b)⌋₊

/-- The selected source sizes tend to infinity with the padded size. -/
theorem paddingIndex_tendsto {A b : ℝ} (hA : 0 < A) (hb : 0 < b) :
    Tendsto (paddingIndex (A := A) (b := b)) atTop atTop := by
  unfold paddingIndex
  apply tendsto_nat_floor_atTop.comp
  exact (tendsto_rpow_atTop (one_div_pos.mpr hb)).comp
    (tendsto_natCast_atTop_atTop.atTop_div_const hA)

/-- The selected source size fits the prescribed target size, including at zero. -/
theorem paddingIndex_bound {A b : ℝ} (hA : 0 < A) (hb : 0 < b) (N : ℕ) :
    A * (paddingIndex (A := A) (b := b) N : ℝ) ^ b ≤ N := by
  unfold paddingIndex
  have hbase : 0 ≤ (N : ℝ) / A := by positivity
  have hp := Real.rpow_le_rpow (by positivity) (Nat.floor_le (Real.rpow_nonneg hbase (1 / b))) hb.le
  rw [← Real.rpow_mul hbase, one_div_mul_cancel hb.ne', Real.rpow_one] at hp
  exact (le_div_iff₀ hA).mp hp |>.trans_eq' (mul_comm _ _)

private theorem floor_scale_growth {A b ε ε' : ℝ} (hA : 0 < A) (hb : 0 < b)
    (hε : 0 < ε) (hgap : ε' < ε / b) (c : ℝ) :
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ ε' ≤ (⌊((N : ℝ) / A) ^ (1 / b)⌋₊ : ℝ) ^ ε := by
  let K := A ^ (ε / b) * (2 : ℝ) ^ ε
  have hK : 0 < K := by dsimp [K]; positivity
  have hg : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (ε / b - ε')) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hgap)).comp tendsto_natCast_atTop_atTop
  have hx : Tendsto (fun N : ℕ ↦ ((N : ℝ) / A) ^ (1 / b)) atTop atTop :=
    (tendsto_rpow_atTop (one_div_pos.mpr hb)).comp
      (tendsto_natCast_atTop_atTop.atTop_div_const hA)
  filter_upwards [hg.eventually_ge_atTop (c * K), hx.eventually_ge_atTop 2,
    eventually_ge_atTop 1] with N hlarge hxlarge hN
  have hpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hbase : 0 ≤ (N : ℝ) / A := by positivity
  change c * K ≤ (N : ℝ) ^ (ε / b - ε') at hlarge
  rw [Real.rpow_sub hpos] at hlarge
  have hmain := (le_div_iff₀ (Real.rpow_pos_of_pos hpos ε')).mp hlarge
  calc
    c * (N : ℝ) ^ ε' ≤ (N : ℝ) ^ (ε / b) / K := by
      apply (le_div_iff₀ hK).mpr
      simpa [mul_right_comm] using hmain
    _ = (((N : ℝ) / A) ^ (1 / b) / 2) ^ ε := by
      rw [Real.div_rpow (Real.rpow_nonneg hbase _) (by norm_num), ← Real.rpow_mul hbase,
        show (1 / b) * ε = ε / b by ring, Real.div_rpow hpos.le hA.le]
      exact (div_div _ _ _).symm
    _ ≤ _ := by
      apply Real.rpow_le_rpow (by positivity) _ hε.le
      have hf := Nat.sub_one_lt_floor (((N : ℝ) / A) ^ (1 / b))
      change 2 ≤ ((N : ℝ) / A) ^ (1 / b) at hxlarge
      linarith

private theorem eventually_poly_overhead_le {C r : ℝ} (hC : 0 < C) (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, C * ((N : ℝ) + 1) ^ 2 ≤ 2 ^ ((N : ℝ) ^ r) := by
  have hT := (tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop
  have hsmall := (isLittleO_rpow_exp_pos_mul_atTop (2 / r) (Real.log_pos (by norm_num : (1 : ℝ) < 2))).comp_tendsto hT
  have hbound := hsmall.bound (show 0 < (4 * C)⁻¹ by positivity)
  filter_upwards [hbound, eventually_ge_atTop 1] with N hN hN1
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hpow : ((N : ℝ) ^ r) ^ (2 / r) = (N : ℝ) ^ 2 := by
    rw [← Real.rpow_mul (Nat.cast_nonneg _), mul_div_cancel₀ _ hr.ne', Real.rpow_two]
  change ‖((N : ℝ) ^ r) ^ (2 / r)‖ ≤ (4 * C)⁻¹ * ‖Real.exp (Real.log 2 * (N : ℝ) ^ r)‖ at hN
  rw [hpow, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (Real.exp_pos _).le,
      ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] at hN
  have hmul : 4 * C * (N : ℝ) ^ 2 ≤ 2 ^ ((N : ℝ) ^ r) := by
    calc
      _ ≤ (4 * C) * ((4 * C)⁻¹ * 2 ^ ((N : ℝ) ^ r)) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
      _ = _ := by field_simp
  calc
    C * ((N : ℝ) + 1) ^ 2 ≤ C * ((N : ℝ) + N) ^ 2 := by gcongr
    _ = 4 * C * (N : ℝ) ^ 2 := by ring
    _ ≤ _ := hmul

/-- Absorb the quadratic cost of homogeneous specialization once the exponent
at the source size dominates the exponent sought at the padded size. -/
private theorem eventually_le_of_projected_bound {C r : ℝ} (hC : 0 < C) (hr : 0 < r)
    {e s : ℕ → ℝ} (hlarge : ∀ᶠ N : ℕ in atTop, 4 * (N : ℝ) ^ r ≤ e N)
    (hproj : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ (e N) ≤ C * ((N : ℝ) + 1) ^ 2 * (1 + s N)) :
    ∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ ((N : ℝ) ^ r) ≤ s N := by
  filter_upwards [eventually_poly_overhead_le hC hr, hlarge, hproj, eventually_ge_atTop 1] with
    N hpoly hlarge hproj hN1
  let a : ℝ := (N : ℝ) ^ r
  have ha : 1 ≤ a := Real.one_le_rpow (by exact_mod_cast hN1) hr.le
  have ha' : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have h2a : 1 ≤ (2 : ℝ) ^ a := Real.one_le_rpow (by norm_num) ha'.le
  have hcost : 0 < C * ((N : ℝ) + 1) ^ 2 := by positivity
  by_contra! hsmall
  have hlt : (2 : ℝ) ^ (e N) < 2 ^ (3 * a) := calc
    _ ≤ _ := hproj
    _ < C * ((N : ℝ) + 1) ^ 2 * (1 + 2 ^ a) := by gcongr
    _ ≤ 2 ^ a * (1 + 2 ^ a) := mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ ≤ 2 ^ a * ((2 : ℝ) * 2 ^ a) := by gcongr; linarith
    _ = (2 : ℝ) ^ (a + 1 + a) := by rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_one]; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hle : (2 : ℝ) ^ (3 * a) ≤ 2 ^ (e N) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by change 4 * a ≤ e N at hlarge; linarith)
  exact (not_lt_of_ge hle) hlt

/-- The transfer only needs a projection from the one source size selected for each
target. Projections from every smaller source size may belong to different targets. -/
theorem borderSize_lower_of_indexed_padding {source target : ℕ → ℕ} {A b C ε ε' : ℝ}
    (hA : 0 < A) (hb : 0 < b) (hC : 0 < C) (hε : 0 < ε)
    (hε' : 0 < ε') (hgap : ε' < ε / b)
    (hlower : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((n : ℝ) ^ ε) ≤ source n)
    (hprojection : ∀ᶠ N : ℕ in atTop, (source (paddingIndex (A := A) (b := b) N) : ℝ) ≤
      C * ((N : ℝ) + 1) ^ 2 * (1 + (target N : ℝ))) :
    ∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ ((N : ℝ) ^ ε') ≤ target N := by
  apply eventually_le_of_projected_bound hC hε' (floor_scale_growth hA hb hε hgap 4)
  filter_upwards [(paddingIndex_tendsto hA hb).eventually hlower, hprojection] with N hN hp
  exact hN.trans hp

/-- A stretched exponential lower bound for the source degree-component border
size transfers to the target as soon as padding supplies the paper's quadratic
specialization inequality. The exponent may be any `0 < ε' < ε / b`. -/
theorem borderSize_lower_of_polynomial_padding {source target : ℕ → ℕ} {A b C ε ε' : ℝ}
    (hA : 0 < A) (hb : 0 < b) (hC : 0 < C) (hε : 0 < ε)
    (hε' : 0 < ε') (hgap : ε' < ε / b)
    (hlower : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((n : ℝ) ^ ε) ≤ source n)
    (hprojection : ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, A * (n : ℝ) ^ b ≤ N →
      (source n : ℝ) ≤ C * ((N : ℝ) + 1) ^ 2 * (1 + (target N : ℝ))) :
    ∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ ((N : ℝ) ^ ε') ≤ target N := by
  apply borderSize_lower_of_indexed_padding hA hb hC hε hε' hgap hlower
  exact hprojection.mono fun N hp ↦ hp _ (paddingIndex_bound hA hb N)

end SpectralBooks
end LinearAlgebra
end OAI

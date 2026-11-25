import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# The grid size contradiction in the proof that every characteristic is Plane

The grid for a bipartite graph on `n` vertices has one site per row-column
intersection and two ends per line. For a fixed positive border lower-bound
exponent, we choose the subdivision parameter before taking `n` to infinity.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter

/-- The number of sites of the independent-set grid, in terms of the sizes
of the two vertex classes, obeys the quadratic estimate in the phase proof. -/
theorem bipartite_grid_size_le {u v n : ℕ} (h : u + v = n) :
    ((u * v + 2 * n : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / 4 + 2 * n := by
  subst n
  push_cast
  nlinarith [sq_nonneg ((u : ℝ) - v)]

/-- The subdivision base can be fixed so the exponent of the quadratic grid
is strictly below the border-size exponent. -/
theorem exists_base_two_logb_ten_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : ℕ, 2 ≤ a ∧ 2 * Real.logb a 10 < δ := by
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop
    (2 * Real.log 10 / δ)
  obtain ⟨a, ha, hlarge⟩ := ((eventually_ge_atTop (2 : ℕ)).and hlog).exists
  have ha' : (1 : ℝ) < a := by exact_mod_cast Nat.lt_of_succ_le ha
  refine ⟨a, ha, ?_⟩
  rw [Real.logb, ← mul_div_assoc, div_lt_iff₀ (Real.log_pos ha')]
  simpa only [Function.comp_apply, mul_comm δ] using (div_lt_iff₀ hδ).mp hlarge

/-- On a quadratic-size grid, a fixed power of the number of sites times its
logarithm is eventually smaller than any strictly higher power of `n`. -/
theorem eventually_grid_exponent_lt {N : ℕ → ℕ} {p δ C : ℝ}
    (hp : 0 ≤ p) (hgap : 2 * p < δ) (hC : 0 < C)
    (hgrid : ∀ᶠ n : ℕ in atTop, 0 < N n ∧ (N n : ℝ) ≤ (n : ℝ) ^ 2 / 4 + 2 * n) :
    ∀ᶠ n : ℕ in atTop, C * (N n : ℝ) ^ p * Real.log (2 * N n) < (n : ℝ) ^ δ := by
  have hsmall := ((isLittleO_log_rpow_atTop (sub_pos.mpr hgap)).const_mul_left
    (2 * C)).comp_tendsto tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < ‖(n : ℝ) ^ (δ - 2 * p)‖ := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  filter_upwards [hgrid, eventually_ge_atTop 8,
    hsmall.eventuallyLT_norm_of_eventually_pos hpos] with n hn h8 hlog
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast h8
  have hnpos : (0 : ℝ) < n := by linarith
  have hNpos : (0 : ℝ) < N n := Nat.cast_pos.mpr hn.1
  have hN2 : 2 * (N n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [hn.2, mul_nonneg hnpos.le (sub_nonneg.mpr hn8)]
  have hN : (N n : ℝ) ≤ (n : ℝ) ^ 2 := by linarith
  have hNpow : (N n : ℝ) ^ p ≤ (n : ℝ) ^ (2 * p) := by
    convert Real.rpow_le_rpow hNpos.le hN hp using 1
    exact Real.rpow_natCast_mul hnpos.le 2 p
  have hNlog : Real.log (2 * (N n : ℝ)) ≤ 2 * Real.log n := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 2) hNpos) hN2
  have hnlog := Real.log_nonneg (show (1 : ℝ) ≤ n by linarith)
  change ‖2 * C * Real.log n‖ < ‖(n : ℝ) ^ (δ - 2 * p)‖ at hlog
  rw [Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le _)] at hlog
  calc
    C * (N n : ℝ) ^ p * Real.log (2 * N n)
        ≤ C * (N n : ℝ) ^ p * (2 * Real.log n) := by gcongr
    _ ≤ C * (n : ℝ) ^ (2 * p) * (2 * Real.log n) := by gcongr
    _ = (n : ℝ) ^ (2 * p) * (2 * C * Real.log n) := by ring
    _ < (n : ℝ) ^ (2 * p) * (n : ℝ) ^ (δ - 2 * p) :=
      mul_lt_mul_of_pos_left hlog (Real.rpow_pos_of_pos hnpos _)
    _ = (n : ℝ) ^ δ := by rw [← Real.rpow_add hnpos]; congr 1; ring

/-- No exact and degree-`n` border circuit sizes can satisfy both the
compression estimate for every fixed base and the Tree lower bound on the
same graph family. The constants and eventual thresholds may depend on the
base. -/
theorem grid_circuit_size_bounds_incompatible (N exactSize borderSize : ℕ → ℕ)
    (hgrid : ∀ᶠ n : ℕ in atTop, 0 < N n ∧ (N n : ℝ) ≤ (n : ℝ) ^ 2 / 4 + 2 * n)
    (hborder : ∀ᶠ n : ℕ in atTop, borderSize n ≤ exactSize n)
    (hupper : ∀ a : ℕ, 2 ≤ a → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (exactSize n : ℝ) ≤ (2 : ℝ) ^ (C * (N n : ℝ) ^ Real.logb a 10 * Real.log (2 * N n)))
    {δ : ℝ} (hδ : 0 < δ)
    (hlower : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((n : ℝ) ^ δ) ≤ (borderSize n : ℝ)) :
    False := by
  obtain ⟨a, ha, hgap⟩ := exists_base_two_logb_ten_lt hδ
  obtain ⟨C, hC, hsize⟩ := hupper a ha
  have ha' : (1 : ℝ) < a := by exact_mod_cast Nat.lt_of_succ_le ha
  have hne := eventually_grid_exponent_lt (Real.logb_nonneg ha' (by norm_num)) hgap hC hgrid
  obtain ⟨n, hn, hl, hb, hu⟩ := (hne.and (hlower.and (hborder.and hsize))).exists
  have hbe : (borderSize n : ℝ) ≤ (exactSize n : ℝ) := by exact_mod_cast hb
  exact (Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hn).not_ge
    (hl.trans (hbe.trans hu))

end SpectralBooks
end LinearAlgebra
end OAI

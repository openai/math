import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace OAI
/-! # Uniform size of the physical selector-mask check -/

namespace Hierarchy.Tagged

open Filter Real

theorem eventual_selector_budget (b : ℝ) (hb : 0 < b) :
    ∀ᶠ h : ℕ in atTop, ∀ s : ℕ, 0 < s → Real.logb 2 s ≤ (h:ℝ)^b →
      (Nat.log 2 (s+1)+2)^3 ≤ 2^h := by
  have o := (isLittleO_rpow_exp_pos_mul_atTop (b*3)
    (Real.log_pos (by norm_num : (1:ℝ)<2))).comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [o.bound (show (0:ℝ)<1/64 by norm_num), eventually_ge_atTop (1:ℕ)] with h cost hh
  intro s hs ls
  have hreal : (1:ℝ) ≤ h := by exact_mod_cast hh
  have ss : 0<(s:ℝ) := by exact_mod_cast hs
  have sq : (1:ℝ) ≤ s := by exact_mod_cast hs
  have pow1 := Real.one_le_rpow hreal hb.le
  have ln := Real.natLog_le_logb (s+1) 2
  push_cast at ln
  have ext := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (show 0<(s:ℝ)+1 by positivity) (show (s:ℝ)+1 ≤ 2*s by linarith)
  rw [Real.logb_mul (by norm_num : (2:ℝ)≠0) ss.ne', Real.logb_self_eq_one (by norm_num)] at ext
  have L : (Nat.log 2 (s+1):ℝ)+2 ≤ 4*(h:ℝ)^b := by linarith
  change ‖(h:ℝ)^(b*3)‖ ≤ 1/64*‖Real.exp (Real.log 2*h)‖ at cost
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
    ← Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2), Real.rpow_natCast] at cost
  have p : ((h:ℝ)^b)^3 = (h:ℝ)^(b*3) := by
    rw [Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_ofNat]
  have scalar : ((Nat.log 2 (s+1):ℝ)+2)^3 ≤ (2:ℝ)^h := calc
    _ ≤ (4*(h:ℝ)^b)^3 := by gcongr
    _ = 64*((h:ℝ)^b)^3 := by ring
    _ ≤ _ := by rw [p]; linarith
  exact_mod_cast scalar

end Hierarchy.Tagged

end OAI

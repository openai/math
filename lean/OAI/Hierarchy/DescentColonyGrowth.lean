import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace OAI
/-! # Dyadic decay absorbs the floor-spaced branching of a colony -/

namespace Hierarchy.DescentColonyGrowth
open scoped BigOperators

theorem positive_gap (Δ : ℕ) (hΔ : 2≤Δ) : 0 < 32*Nat.clog 2 (2*Δ) :=
  Nat.mul_pos (by decide) (Nat.clog_pos (by decide) (by omega))

theorem gap_growth_le (Δ s : ℕ) (hΔ : 2≤Δ) :
    (Δ:ℝ)^(s/(32*Nat.clog 2 (2*Δ))) / (Real.sqrt 2)^s ≤ (9/10:ℝ)^s := by
  let D := 32*Nat.clog 2 (2*Δ)
  have dyadic : (Δ:ℝ) ≤ (2:ℝ)^Nat.clog 2 (2*Δ) := by
    exact_mod_cast (show Δ ≤ 2 ^ Nat.clog 2 (2*Δ) from
      le_trans (by omega : Δ≤2*Δ) (Nat.le_pow_clog (by decide) _))
  have growth : (Δ:ℝ) ≤ (5/4:ℝ)^D := by
    rw [show D=32*Nat.clog 2 (2*Δ) by rfl,pow_mul]
    exact dyadic.trans (pow_le_pow_left₀ (by norm_num) (by norm_num : (2:ℝ)≤(5/4)^32) _)
  have hpow : (Δ:ℝ)^(s/D) ≤ (5/4:ℝ)^s := calc
    _ ≤ ((5/4:ℝ)^D)^(s/D) := pow_le_pow_left₀ (by positivity) growth _
    _ = (5/4:ℝ)^(D*(s/D)) := (pow_mul _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by simpa [Nat.mul_comm] using Nat.div_mul_le_self s D)
  have half : (5/4:ℝ)/Real.sqrt 2 ≤ 9/10 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.sqrt 2)).mpr
    have root : (25/18:ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
    linarith
  calc
    _ ≤ (5/4:ℝ)^s / (Real.sqrt 2)^s := div_le_div_of_nonneg_right hpow (by positivity)
    _ = ((5/4:ℝ)/(Real.sqrt 2))^s := (div_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) half _

theorem sum_gap_growth (Δ k : ℕ) (hΔ : 2≤Δ) :
    ∑ s ∈ Finset.range k, (Δ:ℝ)^(s/(32*Nat.clog 2 (2*Δ))) / (Real.sqrt 2)^s ≤ 10 := by
  calc
    _ ≤ ∑ s ∈ Finset.range k, (9/10:ℝ)^s :=
      Finset.sum_le_sum fun s _ => gap_growth_le Δ s hΔ
    _ ≤ 10 := by
      have h := geom_sum_mul_neg (9/10:ℝ) k
      have pos : 0 ≤ (9/10:ℝ)^k := by positivity
      linarith

end Hierarchy.DescentColonyGrowth

end OAI

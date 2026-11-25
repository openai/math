import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # The cost recurrence for integral convolution

In the integral descent the shorter lengths have logarithm at most a fixed
power less than one of the parent logarithm. The input and output maps add
a power of the logarithm of that logarithm. This file closes the recurrence
of Section 9 of *Near-square-root logarithmic overhead for integer
multiplication and exact transforms*.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Filter Real
open scoped Topology

/-- The predecessor manuscript's function `Gβ`, extended constantly below 3. -/
noncomputable def convolutionGauge (β t : ℝ) : ℝ :=
  (max 3 t)^β * (Real.log (max 3 t))^(2-β)

theorem convolutionGauge_one_le {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 1) (t : ℝ) :
    1 ≤ convolutionGauge β t := by
  have ht : (3 : ℝ) ≤ max 3 t := le_max_left _ _
  have hlog : 1 ≤ Real.log (max 3 t) :=
    (Real.le_log_iff_exp_le (by linarith)).2 (Real.exp_one_lt_three.le.trans ht)
  exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by linarith) hβ)
    (Real.one_le_rpow hlog (by linarith))

private lemma gauge_mono {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 1) : Monotone (convolutionGauge β) := by
  intro t u htu
  have ht : (0 : ℝ) < max 3 t := (by norm_num : (0 : ℝ) < 3).trans_le (le_max_left _ _)
  have hlog : 0 ≤ Real.log (max 3 t) := Real.log_nonneg ((by norm_num : (1:ℝ) ≤ 3).trans (le_max_left _ _))
  unfold convolutionGauge
  gcongr
  · linarith

private theorem eventually_gauge_child {β σ C : ℝ} (hβ : 0 < β) (hβ' : β ≤ 1)
    (hσ : 0 < σ) (hσ' : σ < 1) (hC : 0 < C) :
    ∀ᶠ t : ℝ in atTop, C * (Real.log t)^3 * convolutionGauge β (t^σ) ≤ convolutionGauge β t / 4 := by
  have he : 0 < β - σ*β := by nlinarith [mul_pos (sub_pos.mpr hσ') hβ]
  have ha := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) he).bound
    (show 0 < (4*C)⁻¹ by positivity)
  filter_upwards [ha, eventually_ge_atTop (3 : ℝ), (tendsto_rpow_atTop hσ).eventually_ge_atTop 3]
    with t h ht hpow
  have ht' : 0 < t := by linarith
  have hl : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hl' : 0 ≤ Real.log (t ^ σ) := Real.log_nonneg (by linarith)
  have hbound : (Real.log t)^3 ≤ (4*C)⁻¹ * t^(β-σ*β) := by
    have hcub : (Real.log t)^(3 : ℝ) = (Real.log t)^(3 : ℕ) := Real.rpow_natCast _ 3
    simpa only [hcub, Real.norm_of_nonneg (by positivity : 0 ≤ (Real.log t)^3),
      Real.norm_of_nonneg (Real.rpow_nonneg ht'.le _)] using h
  have hchild : Real.log (t^σ) ≤ Real.log t := by rw [Real.log_rpow ht']; nlinarith
  have hb : (Real.log (t^σ))^(2-β) ≤ (Real.log t)^(2-β) :=
    Real.rpow_le_rpow hl' hchild (by linarith)
  simp only [convolutionGauge, max_eq_right ht, max_eq_right hpow, ← Real.rpow_mul ht'.le]
  calc
    _ ≤ C * ((4*C)⁻¹ * t^(β-σ*β)) * (t^(σ*β) * (Real.log t)^(2-β)) := by gcongr
    _ = (C * (4*C)⁻¹) * (t^(β-σ*β) * t^(σ*β)) * (Real.log t)^(2-β) := by ring
    _ = _ := by
      rw [← Real.rpow_add ht', sub_add_cancel]
      field_simp

/-- The argument applies to any normalized cost. A maximizing child of
`1 + max_{1≤j≤s} D(j)/j` gives the witness `j` in the recurrence. -/
theorem convolution_recurrence_bound {f : ℕ → ℝ} {β σ C : ℝ} (hβ : 0 < β)
    (hβ' : β ≤ 1) (hσ : 0 < σ) (hσ' : σ < 1) (hC : 0 < C)
    (hrec : ∀ᶠ n : ℕ in atTop, ∃ j : ℕ, 0 < j ∧ Real.log j ≤ (Real.log n)^σ ∧
      f n ≤ C * (convolutionGauge β (Real.log n) + (Real.log (Real.log n))^3 * (1 + f j))) :
    ∃ K > (0 : ℝ), ∀ n : ℕ, f n ≤ K * convolutionGauge β (Real.log n) := by
  have htop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨n₀, hbig⟩ := eventually_atTop.mp
    ((hrec.and (htop.eventually (eventually_gauge_child hβ hβ' hσ hσ' hC))).and
      (htop.eventually_gt_atTop 3))
  let S := ∑ j ∈ Finset.range n₀, |f j|
  let K := max (1 + S) (2*C)
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hK : 1 ≤ K := (le_add_of_nonneg_right hS).trans (le_max_left _ _)
  have hKC : 2*C ≤ K := le_max_right _ _
  refine ⟨K, zero_lt_one.trans_le hK, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < n₀
    · have hv : |f n| ≤ S := Finset.single_le_sum (fun j _ => abs_nonneg (f j)) (Finset.mem_range.mpr hn)
      have hv' : f n ≤ K := (le_abs_self _).trans (hv.trans ((by linarith : S ≤ 1+S).trans (le_max_left _ _)))
      exact hv'.trans (le_mul_of_one_le_right (by linarith) (convolutionGauge_one_le hβ.le hβ' _))
    · obtain ⟨⟨⟨j, hj, hshort, hstep⟩, hcheap⟩, ht⟩ := hbig n (by omega)
      change 3 < Real.log (n : ℝ) at ht
      have ht' : 1 < Real.log n := by linarith
      have hshort' : Real.log j < Real.log n := hshort.trans_lt
        ((Real.rpow_lt_rpow_of_exponent_lt ht' hσ').trans_eq (Real.rpow_one _))
      have hjn : j < n := by
        by_contra! hle
        have hnpos : (0 : ℝ) < n := by
          by_contra! hz
          have h0 : (n : ℝ) = 0 := le_antisymm hz (Nat.cast_nonneg n)
          rw [h0, Real.log_zero] at ht
          linarith
        exact hshort'.not_ge (Real.log_le_log hnpos (by exact_mod_cast hle))
      have hg := gauge_mono hβ.le hβ' hshort
      have hsub := (ih j hjn).trans (mul_le_mul_of_nonneg_left hg (by linarith))
      have hone := (convolutionGauge_one_le hβ.le hβ' ((Real.log n)^σ)).trans
        (le_mul_of_one_le_left ((convolutionGauge_one_le hβ.le hβ' ((Real.log n)^σ)).trans' zero_le_one) hK)
      have hcoef : 0 ≤ C * (Real.log (Real.log n))^3 := by
        have := Real.log_pos ht'
        positivity
      have hm := mul_le_mul_of_nonneg_left (add_le_add hone hsub) hcoef
      change C * (Real.log (Real.log n))^3 * convolutionGauge β ((Real.log n)^σ) ≤
        convolutionGauge β (Real.log n) / 4 at hcheap
      have hhalf := mul_le_mul_of_nonneg_left hcheap (show 0 ≤ 2*K by linarith)
      have hweight := mul_le_mul_of_nonneg_right hKC
        (show 0 ≤ convolutionGauge β (Real.log n) by linarith [convolutionGauge_one_le hβ.le hβ' (Real.log n)])
      linarith only [hstep, hm, hhalf, hweight]

end FiniteFourier
end LinearAlgebra
end OAI

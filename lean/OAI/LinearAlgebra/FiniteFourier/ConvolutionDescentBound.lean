import OAI.LinearAlgebra.FiniteFourier.ConvolutionEnvelope
import OAI.LinearAlgebra.FiniteFourier.OpenConvolutionCompile

/-! # From open integral reductions to the convolution upper bound

Each open gate is an ordinary shorter convolution. Compiling it incurs its
actual integral circuit cost. The sum of the shorter lengths is at most 540
times the parent length. The normalized costs therefore obey the recurrence
used in the polynomial-convolution theorem.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Filter

/-- The open reduction and pre/postprocessing estimates used in Section 9.
The child bound `s` controls both the actual shorter gates and the fixed-operand
convolutions charged to the linear input and output maps. -/
def IntegralOpenDescent (β : ℝ) : Prop :=
  ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∃ (s : ℕ) (B : Type) (_ : Fintype B) (len : B → ℕ) (p : OpenConvolution ℤ n B len),
      0 < s ∧ Real.log s ≤ (Real.log n)^σ ∧
      (∀ i, 0 < len i ∧ len i ≤ s) ∧ (∑ i, len i) ≤ 540*n ∧ p.RealizesMultiple 1 ∧
      (p.linearCost : ℝ) / n ≤ C * (convolutionGauge β (Real.log n) +
        (Real.log (Real.log n))^3 * convolutionEnvelope s)

/-- Open integral descent with the stated uniform overhead gives actual
division-free integral programs over every equal length. -/
theorem IntegralOpenDescent.integralConvolutionBound {β α : ℝ} (h : IntegralOpenDescent β)
    (hβ : 0 < β) (hβ' : β ≤ 1) (hβα : β < α) :
    ∃ D > (0 : ℝ), IntegralConvolutionBound α D := by
  obtain ⟨σ, hσ, hσ', C, hC, hstep⟩ := h
  apply integralConvolutionBound_of_recurrence hβ hβ' hβα hσ hσ'
    (by positivity : 0 < 3*C + 1622)
  have ht := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hstep, (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1,
    eventually_gt_atTop (0 : ℕ)] with n hh hlog hn
  obtain ⟨s, B, hB, len, p, hs, hshort, hlen, hvol, hp, hcost⟩ := hh
  let _ := hB
  refine ⟨s, hs, hshort, ?_⟩
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let G := convolutionGauge β (Real.log n)
  let A := (Real.log (Real.log n))^3
  let E := convolutionEnvelope s
  have hG : 1 ≤ G := convolutionGauge_one_le hβ.le hβ' _
  have hA : 1 ≤ A := one_le_pow₀ hlog
  have hE : 1 ≤ E := convolutionEnvelope_one_le hs
  have hAE : E ≤ A * E := le_mul_of_one_le_left (zero_le_one.trans hE) hA
  have hcomp := p.integralConvolutionCost_le hp
  have hsum : (∑ i, (integralConvolutionCost (len i) : ℝ)) ≤ (∑ i, (len i : ℝ)) * E := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hi := convolutionRate_le_envelope (hlen i).1 (hlen i).2
    have hlen' : 0 < (len i : ℝ) := by exact_mod_cast (hlen i).1
    exact ((div_le_iff₀ hlen').mp hi).trans_eq (mul_comm ..)
  have hvol' : (∑ i, (len i : ℝ)) ≤ 540 * n := by exact_mod_cast hvol
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_right hvol' (zero_le_one.trans hE))
  have hlin : (p.linearCost : ℝ) ≤ C * (G + A*E) * n := (div_le_iff₀ hn').mp hcost
  have hsize : (integralConvolutionCost n : ℝ) ≤ 3*p.linearCost +
      2*(∑ i, (len i : ℝ)) + 2*n + ∑ i, (integralConvolutionCost (len i) : ℝ) := by
    have hcomp' : (integralConvolutionCost n : ℝ) ≤
        3*p.linearCost + 2*(∑ i, (len i : ℝ)) + ((2*n-1 : ℕ) : ℝ) +
        ∑ i, (integralConvolutionCost (len i) : ℝ) := by exact_mod_cast hcomp
    have hreg : ((2*n-1 : ℕ) : ℝ) ≤ 2*n := by exact_mod_cast Nat.sub_le (2*n) 1
    linarith
  change convolutionRate n ≤ (3*C + 1622)*(G+A*E)
  apply (div_le_iff₀ hn').2
  have hgN := mul_le_mul_of_nonneg_right hG hn'.le
  have hEN := mul_le_mul_of_nonneg_right hAE hn'.le
  have hAE0 : 0 ≤ A*E := mul_nonneg (zero_le_one.trans hA) (zero_le_one.trans hE)
  have hN0 := mul_nonneg hAE0 hn'.le
  linarith only [hsize, hlin, hvol', hsum', hgN, hEN, hN0, hn']

end FiniteFourier
end LinearAlgebra
end OAI

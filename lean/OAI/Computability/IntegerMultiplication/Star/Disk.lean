import OAI.Computability.IntegerMultiplication.Star.Clock

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Star
open scoped BigOperators Real
open Complex Finset IntegerMultiplication.Fourier
noncomputable section

def throttle (x:ℝ) := max (-1:ℝ) (min x 1)
theorem throttle_bound (x) :
    |throttle x|≤1 := by
  apply abs_le.mpr
  exact ⟨le_sup_left,max_le (by norm_num) (min_le_right ..)⟩
theorem throttle_gap {y:ℝ} (h: |y|≤1) (x:ℝ) :
    |throttle x-y|≤ |x-y| := by
  obtain ⟨a,b⟩:=abs_le.mp h
  rcases lt_or_ge x (-1) with s|s
  · rw [throttle, min_eq_left (by linarith),max_eq_left s.le,
      abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)]
    linarith
  rcases lt_or_ge 1 x with t|t
  · rw [throttle,min_eq_right t.le,max_eq_right (by linarith),abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith
  rw [throttle,min_eq_left t,max_eq_right s]

def pin (n:ℕ) (x:ℝ) := throttle (needle n (x/2)).re

theorem cis_half (x:ℝ) :
    (Fourier.cis (x/2)).re = Real.cos (π*x) := by
  rw [Fourier.cis,show x/2*(2*π)=π*x by ring,Complex.exp_mul_I]
  rw [← Complex.ofReal_sin,← Complex.ofReal_cos]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem pointed {n} (h:4≤n) {x:ℝ} (t:|x|≤1):
    |pin n x - Real.cos (π*x)| ≤ (2:ℝ)^34*drop_ n := by
  have L : |x/2|≤1 := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith
  have P:= (throttle_gap (abs_le.mpr ⟨Real.neg_one_le_cos (π*x),Real.cos_le_one _⟩)
    (needle n (x/2)).re)
  refine P.trans ?_
  rw [← cis_half]
  have e := Complex.abs_re_le_norm (needle n (x/2) - Fourier.cis (x/2))
  simpa using e.trans (tip h L)

theorem reach {x y:ℝ} (p : |x|≤1) (h : |y|≤1) (n:ℕ) :
    |x^n-y^n| ≤ n*|x-y| := by
  induction n with
  | zero=>simp
  | succ n ih=>
    rw [pow_succ x,pow_succ y,
      show x^n*x-y^n*y=x^n*(x-y)+(x^n-y^n)*y by ring]
    calc
     _ ≤ |x^n*(x-y)| + |(x^n-y^n)*y| := abs_add_le _ _
     _ ≤ 1*|x-y| + (n*|x-y|)*1 := by
       have t : |x|^n≤1 := pow_le_one₀ (abs_nonneg _) p
       rw [abs_mul,abs_mul,abs_pow]; gcongr
     _ = _ := by push_cast; ring

def sail (n:ℕ) (d:ℕ) (x:ℝ) := (pin n x)^(2*d)
theorem sail_bound (n d x): |sail n d x|≤1 := by
  rw [sail,abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (throttle_bound _)
theorem sails {n} (h:4≤n) {x:ℝ} (t:|x|≤1) (d):
    |sail n d x - Real.cos (π*x)^(2*d)| ≤ (2*d)*(2^34*drop_ n) := by
  unfold sail
  apply (reach (p:= throttle_bound (needle n (x/2)).re) (h:=abs_le.mpr ⟨Real.neg_one_le_cos (π*x),Real.cos_le_one _⟩) (2*d)).trans
  push_cast; exact mul_le_mul_of_nonneg_left (pointed h t) (by positivity)
end
end Star

end IntegerMultiplication
end Computability
end OAI

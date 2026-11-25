import OAI.Hierarchy.TaggedApproximation
import Mathlib.Tactic

namespace OAI
/-! # Combining the pass count with local and packed call prices -/
namespace Hierarchy.Tagged.Radix

theorem pass_bill {h c n : ℕ} {a x y A U C : ℝ}
    (hh : 1≤h) (ha : 1<a) (hx : 0≤x) (hA : 0<A) (hU : 0<U) (hC : 0<C)
    (count : ((n+1:ℕ):ℝ) ≤ C*(h:ℝ)^(1-1/a)) :
    ((n+1:ℕ):ℝ)*(2*(c:ℝ)*((2:ℝ)^h*h) + 2*(A*work h h (x/a))+U*work h h y) ≤
      C*(2*(c:ℝ)+2*A+U)*work h h (1-1/a+max (x/a) y) := by
  let b := (2:ℝ)^h*h
  let e := max (x/a) y
  have hb : 0≤b := by dsimp [b]; positivity
  have hpos : 0 < (h:ℝ) := by exact_mod_cast (zero_lt_one.trans_le hh)
  have hone : 1 ≤ (h:ℝ) := by exact_mod_cast hh
  have he : 0 ≤ e := (div_nonneg hx (by linarith)).trans (le_max_left _ _)
  have first : work h h (x/a) ≤ b*(h:ℝ)^e := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hone (le_max_left _ _)) hb
  have second : work h h y ≤ b*(h:ℝ)^e := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hone (le_max_right _ _)) hb
  have basis : b ≤ b*(h:ℝ)^e := le_mul_of_one_le_right hb (Real.one_le_rpow hone he)
  let bill := 2*(c:ℝ)+2*A+U
  have normal : 2*(c:ℝ)*b+2*(A*work h h (x/a))+U*work h h y ≤ bill*(b*(h:ℝ)^e) := by
    dsimp only [bill]
    linarith only [mul_le_mul_of_nonneg_left first (show 0≤2*A by positivity),
      mul_le_mul_of_nonneg_left second hU.le,mul_le_mul_of_nonneg_left basis (show 0≤2*(c:ℝ) by positivity)]
  have paid := mul_le_mul count normal
    (show 0≤2*(c:ℝ)*b+2*(A*work h h (x/a))+U*work h h y by unfold work; positivity)
    (show 0≤C*(h:ℝ)^(1-1/a) by positivity)
  calc
    _ ≤ (C*(h:ℝ)^(1-1/a))*(bill*(b*(h:ℝ)^e)) := paid
    _ = _ := by
      dsimp [work,b,bill,e]
      rw [Real.rpow_add hpos]
      ring

end Hierarchy.Tagged.Radix

end OAI

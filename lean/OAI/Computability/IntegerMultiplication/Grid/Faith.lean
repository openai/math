import OAI.Computability.IntegerMultiplication.Grid.Value

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Grid
open Finset
private theorem clips (n:ℕ) (x:ℤ) :
    |(x:ℝ) - (slash n x:ℤ)*(2:ℝ)^n| ≤ (2:ℝ)^n := by
  have h : |x - slash n x*(2:ℤ)^n| ≤ 2^n := by
    unfold slash
    have s : x=x.sign*(x.natAbs:ℕ) := (Int.sign_mul_natAbs ..).symm
    nth_rw 1 [s]
    rw [mul_assoc, ← mul_sub, abs_mul]
    have e : |x.sign| ≤ 1 := by
      rcases lt_trichotomy (0:ℤ) x with h|h|h
      · simp [Int.sign_eq_one_of_pos h]
      · simp [← h]
      simp [Int.sign_eq_neg_one_of_neg h]
    let q : ℕ := x.natAbs
    have law : q = q /2^n*2^n+q%2^n := (Nat.div_add_mod' ..).symm
    have e2 : (q:ℤ)-((q/2^n:ℕ):ℤ)*2^n=↑(q%2^n) := by
      apply sub_eq_of_eq_add
      exact_mod_cast (law.trans (Nat.add_comm ..))
    change _ * |(q:ℤ)-((q/2^n:ℕ):ℤ)*2^n| ≤ _
    rw [e2,abs_of_nonneg (Int.natCast_nonneg _)]
    apply (show _ ≤ (1:ℤ)*(q%2^n:ℕ) from mul_le_mul_of_nonneg_right e (by positivity)).trans
    rw [one_mul]
    exact_mod_cast (Nat.mod_lt q (Nat.pow_pos (by decide))).le
  exact_mod_cast h

theorem slash_limit (k : ℕ) (x : ℤ) :
    |((slash k x:ℤ):ℝ)| ≤ (|((x:ℤ):ℝ)|/(2:ℝ)^k) := by
  rw [le_div_iff₀ (by positivity),slash]; rw [Int.cast_mul,Int.cast_natCast]
  rw [abs_mul]
  have e : |((x.sign:ℤ):ℝ)|≤1 := by
    rcases lt_trichotomy (0:ℤ) x with h|h|h
    · simp only [Int.sign_eq_one_of_pos h]; simp
    · simp [← h]
    simp only [Int.sign_eq_neg_one_of_neg h]; simp
  rw [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (x.natAbs/2^k:ℕ))]
  calc
    _ ≤ (1:ℝ)*((x.natAbs/2^k:ℕ):ℝ)*2^k := by gcongr
    _ ≤ ↑x.natAbs := by
      rw [one_mul]
      exact_mod_cast Nat.div_mul_le_self x.natAbs (2^k)
    _ = _ := by rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]

private theorem rs (p) (x) :
    (toC x/(2:ℂ)^p).re=(x.re:ℝ)/(2:ℝ)^p := by
  rw [show (2:ℂ)^p=↑((2:ℝ)^p) by push_cast; rfl,Complex.div_ofReal]
  simp [toC]
private theorem si (p) (x) :
    (toC x/(2:ℂ)^p).im=(x.im:ℝ)/(2:ℝ)^p := by
  rw [show (2:ℂ)^p=↑((2:ℝ)^p) by push_cast; rfl,Complex.div_ofReal]
  simp [toC]
private theorem box (n:ℕ) (x:ℤ) :
    |((slash n x:ℤ):ℝ) - (x:ℝ)/(2:ℝ)^n|≤1 := by
  have s := clips n x
  let e : ℝ := ↑(slash n x)
  have D : 0 < (2:ℝ)^n := by positivity
  rw [show e-(x:ℝ)/(2:ℝ)^n=(e*2^n-x)/(2:ℝ)^n from by field,abs_div, abs_of_pos D,
    div_le_one D] -- lemma
  rw [abs_sub_comm]; exact s

theorem embedded (p:ℕ) (x:Cell) :
    ‖toC (divA p x) - toC x/(2:ℂ)^p‖ ≤ (2:ℝ) := by
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  simp only [Complex.sub_re,Complex.sub_im,rs,si]
  have h (a:Cell) : (toC a).re=(a.re:ℝ) ∧ (toC a).im=(a.im:ℝ) := by simp [toC]
  rw [(h _).1,(h _).2]
  change |((slash p x.re):ℝ)- _|+|((slash p x.im):ℝ)-_|≤_
  linarith [box p x.re,box p x.im]

-- stage phase under normalized post product bounds
open Dusk
variable {k:ℕ}
theorem confident (p:ℕ) (x y:Grain k)
    (h : ‖meaning p k x*meaning p k y‖*(2:ℝ)^p + 2 < (2:ℝ)^k) :
    ‖meaning p k (launch (x,Code.tally p,Dusk.mark y))-meaning p k x*meaning p k y‖ ≤ (2:ℝ)/2^p := by
  let a := aspect x*aspect y
  have H : (toC a)/(2:ℂ)^p /(2:ℂ)^p= meaning p k x* meaning p k y := by
    simp only [a,map_mul,meaning]
    field
  have d := embedded p a
  have u : ‖toC (divA p a)‖ ≤ ‖toC a/(2:ℂ)^p‖ + 2 := by
    have e := norm_add_le (toC a/(2:ℂ)^p) (toC (divA p a)-toC a/(2:ℂ)^p)
    rw [add_sub_cancel ..] at e -- orientation
    linarith
  have e : ‖toC a/(2:ℂ)^p‖= ‖meaning p k x * meaning p k y‖ * 2^p := by
    simp only [← H,norm_div,norm_pow,show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
    field
  rw [meaning,faithful p _ _ (by
    change focus k (divA p a)
    apply short _ (into _)
    rw [e] at u; linarith)]
  rw [← H, ← sub_div,norm_div,norm_pow,show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
  gcongr
end Grid

end IntegerMultiplication
end Computability
end OAI

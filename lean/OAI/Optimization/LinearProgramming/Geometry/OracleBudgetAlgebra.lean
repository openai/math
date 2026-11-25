import Mathlib.Tactic.Ring

/-! Factored natural-number arithmetic for the geometric prefix budget. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace LabelRAM
namespace BudgetAlgebra

theorem cubic_prefix (z : ℕ) (hz : 0 < z) :
    z * (z * (32 * (100 * z^3) + 210) + 33) ≤ 3443 * z^5 := by
  have h₁ : z ≤ z^5 := by simpa only [pow_one] using Nat.pow_le_pow_right hz (show 1≤5 by decide)
  have h₂ : z^2 ≤ z^5 := Nat.pow_le_pow_right hz (by decide)
  calc
    _ = 3200*z^5 + 210*z^2 + 33*z := by ring
    _ ≤ 3200*z^5 + 210*z^5 + 33*z^5 :=
      Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 210 h₂) _) (Nat.mul_le_mul_left 33 h₁)
    _ = (3200+210+33)*z^5 := by rw [Nat.add_mul, Nat.add_mul]
    _ = _ := rfl

theorem fifth_cube_product (z c a : ℕ) : z*(c*(a*z^3)^5) = (c*a^5)*z^16 := by
  rw [mul_pow, ← pow_mul]
  change z*(c*(a^5*z^15)) = (c*a^5)*z^16
  rw [show z^16 = z^15*z from pow_succ z 15]
  ac_rfl

theorem scalar_succ_power (z c d : ℕ) : z*(c*z^d) = c*z^(d+1) := by
  rw [pow_succ]
  ac_rfl

theorem combined_time {r n N C c e post front : ℕ} (hsize : r+n ≤ N)
    (hC : C ≤ c*(N+1)^e) (hfront : front ≤ r*C+3443*(r+n+1)^5)
    (hpost : post ≤ 510000000*(r+n+1)^9) :
    front+post+12 ≤ (c+510004000)*(N+1)^(max (e+1) 9) := by
  let z := N+1
  let d := max (e+1) 9
  have hz : 0 < z := Nat.succ_pos _
  have hdim : r+n+1 ≤ z := Nat.succ_le_succ hsize
  have hr : r ≤ z := (Nat.le_add_right r n).trans (hsize.trans (Nat.le_succ N))
  have h₁ : z^(e+1) ≤ z^d := Nat.pow_le_pow_right hz (le_max_left ..)
  have h₂ : z^9 ≤ z^d := Nat.pow_le_pow_right hz (le_max_right ..)
  have h₅ : (r+n+1)^5 ≤ z^d := (Nat.pow_le_pow_left hdim 5).trans
    (Nat.pow_le_pow_right hz ((show 5≤9 by decide).trans (le_max_right ..)))
  have hrC : r*C ≤ c*z^d := (Nat.mul_le_mul hr hC).trans
    ((scalar_succ_power z c e).le.trans (Nat.mul_le_mul_left c h₁))
  have hprefix := hfront.trans (Nat.add_le_add hrC (Nat.mul_le_mul_left 3443 h₅))
  have hafter := hpost.trans (Nat.mul_le_mul_left 510000000 ((Nat.pow_le_pow_left hdim 9).trans h₂))
  have tail : 12 ≤ 12*z^d := Nat.le_mul_of_pos_right 12 (pow_pos hz d)
  calc
    _ ≤ c*z^d+3443*z^d+510000000*z^d+12*z^d := Nat.add_le_add (Nat.add_le_add hprefix hafter) tail
    _ = (c+3443+510000000+12)*z^d := by rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

theorem combined_width {r n N L extra H l d x f post postExponent front cpre cpost : ℕ}
    (hsize : r+n ≤ N) (hL : L ≤ l*(N+1)^d) (hX : extra ≤ x*(N+1)^f)
    (hfront : front ≤ r*extra+cpre*(r+n+L+1)^16) (hpost : post ≤ cpost*(r+n+1)^postExponent) :
    max (H+front) post ≤ H+(x+cpre*(l+1)^16+cpost)*(N+1)^(max (f+1) (max (max d 1*16) postExponent)) := by
  let z := N+1
  let D := max d 1
  let E := max (f+1) (max (D*16) postExponent)
  have hz : 0 < z := Nat.succ_pos _
  have hdim : r+n+1 ≤ z := Nat.succ_le_succ hsize
  have hr : r ≤ z := (Nat.le_add_right r n).trans (hsize.trans (Nat.le_succ N))
  have hL' := hL.trans (Nat.mul_le_mul_left l (Nat.pow_le_pow_right hz (show d≤D from le_max_left ..)))
  have hZ : z≤z^D := by simpa only [pow_one] using Nat.pow_le_pow_right hz (show 1≤D from le_max_right ..)
  have hlarge : r+n+L+1 ≤ (l+1)*z^D := by
    calc
      _ = (r+n+1)+L := by omega
      _ ≤ z^D + l*z^D := Nat.add_le_add (hdim.trans hZ) hL'
      _ = _ := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  have hx : r*extra ≤ x*z^E := (Nat.mul_le_mul hr hX).trans
    ((scalar_succ_power z x f).le.trans (Nat.mul_le_mul_left x (Nat.pow_le_pow_right hz (le_max_left ..))))
  have hp : cpre*(r+n+L+1)^16 ≤ (cpre*(l+1)^16)*z^E := by
    calc _ ≤ cpre*((l+1)*z^D)^16 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlarge 16)
         _ = (cpre*(l+1)^16)*z^(D*16) := by rw [mul_pow,←pow_mul,Nat.mul_assoc]
         _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hz (le_trans (le_max_left ..) (le_max_right ..)))
  have hex : postExponent≤E := (le_max_right (D*16) postExponent).trans (le_max_right ..)
  have hpost' : post ≤ cpost*z^E := hpost.trans (Nat.mul_le_mul_left cpost
    ((Nat.pow_le_pow_left hdim postExponent).trans (Nat.pow_le_pow_right hz hex)))
  change max _ post ≤ H+(x+cpre*(l+1)^16+cpost)*z^E
  rw [Nat.add_mul, Nat.add_mul]
  apply max_le
  · exact Nat.add_le_add_left (hfront.trans ((Nat.add_le_add hx hp).trans (Nat.le_add_right _ _))) H
  · exact hpost'.trans ((Nat.le_add_left _ _).trans (Nat.le_add_left _ H))

theorem compose_width {r n E G H N c q coef degree w : ℕ}
    (hw : w ≤ H+coef*(r+n+E+G+1)^degree) (hsize : r+n ≤ N) (hloc : E+G ≤ c*(N+1)^q) :
    w ≤ H+(coef*(c+1)^degree)*(N+1)^(max q 1 * degree) := by
  let z := N+1
  let d := max q 1
  have hz : 0<z := Nat.succ_pos _
  have hz' : z≤z^d := by simpa only [pow_one] using Nat.pow_le_pow_right hz (show 1≤d from le_max_right ..)
  have h₁ := hloc.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_right hz (show q≤d from le_max_left ..)))
  have h₂ : r+n+1≤z := Nat.succ_le_succ hsize
  have h₃ : r+n+E+G+1 ≤ (c+1)*z^d := by
    calc
      _ = (r+n+1)+(E+G) := by omega
      _ ≤ z^d+c*z^d := Nat.add_le_add (h₂.trans hz') h₁
      _ = _ := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  apply hw.trans
  apply Nat.add_le_add_left
  calc _ ≤ coef*((c+1)*z^d)^degree := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h₃ degree)
       _ = _ := by rw [mul_pow, ←pow_mul, Nat.mul_assoc]

end BudgetAlgebra
end LabelRAM
end Geometry
end LinearProgramming
end Optimization
end OAI

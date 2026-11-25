import OAI.Computability.IntegerMultiplication.Param.Cut
import OAI.Computability.IntegerMultiplication.Net.Count

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Param
open Net Real
/- Normalize analytic costs against d^32sigma' with lots of slack. -/
noncomputable def alpha:ℝ := 1- (1:ℝ)/(2^120)
noncomputable section
def fund (n:ℕ):ℝ := (lanes n:ℝ)^(32*alpha)
theorem alpha_facts :
    Motif.sigma ≤alpha ∧ alpha≤1 ∧ alpha ≤ (1:ℝ)-(2:ℝ)⁻¹^(182:ℕ) :=
  by norm_num [Motif.sigma,alpha]
theorem allow :
    2*tiny + 32*Motif.sigma ≤ 32*alpha ∧
    tiny + Motif.sigma + 31 ≤ 32*alpha ∧
    1+31*Motif.sigma ≤32*alpha ∧ 31+9/10≤32*alpha :=
  by norm_num [Motif.sigma,alpha,tiny,giant]
theorem apos : 0<alpha := Motif.sigma_range.1.trans_le alpha_facts.1
theorem man n : 1≤(lanes n:ℝ) := by exact_mod_cast (lanes_pos n)

theorem fund1 n : 1 ≤ fund n := Real.one_le_rpow (man n) (mul_nonneg (by norm_num) apos.le)

def reward (n:ℕ):ℝ := (beta n:ℝ)^((1:ℝ)-(2:ℝ)⁻¹^(182:ℕ))
theorem fund_gate n :
    fund n ≤ 2^36 * reward n := by
  unfold fund
  rw [Real.rpow_mul (by positivity)]
  let q:ℝ:=lanes n
  have e : q^(32:ℝ)=q^(32:ℕ) := by simpa only [Nat.cast_ofNat] using Real.rpow_natCast q 32
  change (q^(32:ℝ))^alpha ≤ _
  rw [e]
  have z : q^(32:ℕ) ≤ 2^36*(beta n:ℝ) := by unfold q; exact_mod_cast beyond n
  have h : 1≤(2:ℝ)^(36:ℕ) := by norm_num
  have B : 1≤(beta n:ℝ) := by exact_mod_cast (show 1≤beta n from Nat.le_max_left ..)
  calc
    _ ≤ ((2:ℝ)^36*(beta n:ℝ))^alpha := Real.rpow_le_rpow (by positivity) z apos.le
    _ ≤ _ := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      have w := Real.rpow_le_self_of_one_le h alpha_facts.2.1
      exact mul_le_mul w (Real.rpow_le_rpow_of_exponent_le B alpha_facts.2.2)
        (by positivity) (by norm_num)
-- estimates
theorem under n (a:ℝ) (v:a≤32*alpha) :
    (lanes n:ℝ)^a ≤ fund n :=
  Real.rpow_le_rpow_of_exponent_le (man n) v
theorem ranger n (c : ℕ) (v : (c:ℝ)≤32*alpha) :
    (lanes n:ℝ)^c ≤ fund n := by
  rw [← Real.rpow_natCast]; exact under _ _ v

theorem spanThrifty (n) :
    span_ n + 1 ≤ 2*lanes n^31 := by
  have h:=wall_small n
  have v : lanes n* span_ n ≤ lanes n*lanes n^31 :=
    h.trans (by unfold budget; ring_nf; exact le_rfl)
  have t := Nat.le_of_mul_le_mul_left v (lanes_pos n)
  have X : 1≤lanes n^31 := Nat.pow_pos (lanes_pos n)
  omega
theorem sigma_step {a d : ℝ}
    (x : 1 ≤ d) (y : 0 ≤ a) (z : a ≤ 2*d) :
    a^Motif.sigma ≤ 2*d^Motif.sigma := by
  refine (Real.rpow_le_rpow y z Motif.sigma_range.1.le).trans ?_
  rw [Real.mul_rpow (by norm_num) (by linarith)]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le (by norm_num) Motif.sigma_range.2.le) (by positivity)

-- one column advance stages
theorem heightFare (n):
    ((chunk n+border n:ℝ)+1)*((scouts n+1:ℕ):ℝ)^Motif.sigma *
      ((span_ n:ℝ)+1) ≤ 16*fund n := by
  let d:ℝ:=lanes n
  have h : 1≤d := man n
  have w : (chunk n:ℝ)+border n+1 ≤ 4*d^tiny := by
    have x : (border n:ℝ) ≤ 2*chunk n := by exact_mod_cast (border_v n).2
    have y : 1 ≤ (chunk n:ℝ) := by exact_mod_cast chunk_pos n
    linarith [show (chunk n:ℝ) ≤ d^tiny from chunkCost _]
  have s : ((scouts n+1:ℕ):ℝ)^Motif.sigma ≤ 2*d^Motif.sigma := by
    have x : scouts n ≤ lanes n := Nat.sub_le _ _
    have y : (scouts n:ℝ) ≤ d := by unfold d; exact_mod_cast x
    apply sigma_step h (by positivity); push_cast; linarith
  have v : (span_ n:ℝ)+1≤2*d^(31:ℕ) := by unfold d; exact_mod_cast spanThrifty n
  calc
    _ ≤ 4*d^tiny*(2*d^Motif.sigma)*(2*d^(31:ℕ)) := by gcongr
    _ = 16*d^(tiny+Motif.sigma+31) := by
      have t : (d^(31:ℝ))=d^(31:ℕ) := by simpa only [Nat.cast_ofNat] using (Real.rpow_natCast d 31)
      rw [Real.rpow_add (by linarith : 0<d),Real.rpow_add (by linarith : 0<d),t]; ring
    _ ≤ _ := by gcongr; exact under _ _ allow.2.1

theorem permutationFare {n a K} (v : a≤budget n) (w : K ≤ chunk n) :
    ((K:ℝ)+1)*((a+1:ℕ):ℝ)^Motif.sigma*((K:ℝ)+1) ≤ 8*fund n := by
  let d:ℝ:=lanes n
  have h : 1≤d := man n
  have w' : (K:ℝ)+1 ≤ 2*d^tiny := by
    have q : (K:ℝ)≤chunk n := by exact_mod_cast w
    have p : 1 ≤ (chunk n:ℝ) := by exact_mod_cast chunk_pos n
    linarith [show (chunk n:ℝ)≤d^tiny from chunkCost _]
  have t : ((a+1:ℕ):ℝ) ≤ 2*d^(32:ℕ) := by
    have p : d^(32:ℕ)=(budget n:ℕ) := by unfold d budget; push_cast; rfl
    have q : (a:ℝ) ≤ budget n := by exact_mod_cast v
    rw [p]; push_cast; have e : 1≤(budget n:ℝ) := by exact_mod_cast budget_p n
    linarith [show 1≤(budget n:ℝ) from by exact_mod_cast budget_p n]
  calc
    _ ≤ 2*d^tiny*(2*(d^(32:ℕ))^Motif.sigma)*(2*d^tiny) := by
      have v := sigma_step (one_le_pow₀ h (n:=32)) (Nat.cast_nonneg _) t
      gcongr
    _ = 8*d^(2*tiny+32*Motif.sigma) := by
      have e : d^(32:ℝ)=d^(32:ℕ) := by simpa only [Nat.cast_ofNat] using (Real.rpow_natCast d 32)
      rw [two_mul tiny,Real.rpow_add (by linarith : 0<d),Real.rpow_add (by linarith : 0<d),
        Real.rpow_mul (by linarith : 0≤d),e]
      ring
    _ ≤ _ := by gcongr; exact under _ _ allow.1

theorem relabelFare (n):
    (lanes n:ℝ)*((span_ n+1:ℕ):ℝ)^Motif.sigma ≤ 2*fund n := by
  let d:= (lanes n:ℝ); have h : 1≤d := man n
  have e : ((span_ n+1:ℕ):ℝ)≤ 2*d^(31:ℕ) := by unfold d; exact_mod_cast spanThrifty _
  calc
    _ ≤ d*(2*(d^(31:ℕ))^Motif.sigma) := by
      have i := sigma_step (one_le_pow₀ h (n:=31)) (Nat.cast_nonneg _) e
      change d*_ ≤ _; gcongr
    _ = 2*d^(1+31*Motif.sigma) := by
      rw [Real.rpow_add (by linarith : 0<d),Real.rpow_one,Real.rpow_mul (by linarith : 0≤d)]
      have e : d^(31:ℝ)=d^(31:ℕ) := by simpa only [Nat.cast_ofNat] using (Real.rpow_natCast d 31)
      rw [e]; ring
    _ ≤ _ := by gcongr; exact under _ _ allow.2.2.1
end
end Param

end IntegerMultiplication
end Computability
end OAI

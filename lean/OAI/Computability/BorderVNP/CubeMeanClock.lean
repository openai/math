import OAI.Computability.BorderVNP.CubeScales

/-! # Clock and word capacity of the public incident-row label scan

The native table uses a constant number of instructions per incident record and label-bin trial.
Its costs depend on the number of records, while the integers in its comparisons depend on the
sum of their widths. These bounds keep the two dependencies separate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.MeanChoice

open TeamScales Filter

/-- A simultaneous bound for the initialization, all trial scores and the commit scans.
The alphabet factor allows the three nested loops over a candidate and an ordered bin. -/
def scanEnvelope (K cells degree Z : ℕ) : ℕ := K*(cells+1)*(degree+1)*(Z+1)^6

/-- Under the sparse Section 7.3 descriptor bounds the full label scan is strictly within the
public budget, uniformly for every positive team size. -/
theorem eventually_scanEnvelope {α : ℝ} (hα : 0 < α) (a : ℕ)
    (small : α*a < 1/10^6) (K B : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ r cells degree : ℕ, 1 ≤ r →
      (cells : ℝ) ≤ B*r*(n : ℝ)^(9/10 : ℝ) → (degree : ℝ) ≤ (n : ℝ)^(1/100 : ℝ) →
      (scanEnvelope K cells degree (labelCount α a n) : ℝ) < r*(n : ℝ)^(95/100 : ℝ) := by
  let e : ℝ := 9/10+1/100+4*α*a*6
  have gap : e < 95/100 := by dsimp [e]; linarith only [small]
  let C := (K:ℝ)*(B+1)*2*2^6
  filter_upwards [eventually_labelCount_power hα a 6, eventually_rpow_gap gap (C+1),
    eventually_ge_atTop 1] with n hZ hC hn
  intro r cells degree hr hv hm
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hr' : 1 ≤ (r:ℝ) := by exact_mod_cast hr
  have npos := zero_lt_one.trans_le hn'
  have rpos := zero_lt_one.trans_le hr'
  have oneV : 1 ≤ r*(n:ℝ)^(9/10 : ℝ) := one_le_mul_of_one_le_of_one_le hr' (Real.one_le_rpow hn' (by norm_num))
  have hcells : (cells:ℝ)+1 ≤ (B+1)*r*(n:ℝ)^(9/10:ℝ) := by
    rw [add_mul,one_mul,add_mul]; exact add_le_add hv oneV
  have hdegree : (degree:ℝ)+1 ≤ 2*(n:ℝ)^(1/100:ℝ) := by
    rw [two_mul]; exact add_le_add hm (Real.one_le_rpow hn' (by norm_num))
  have halph : 0 < alphabet α n := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos npos _)
  have hzpos : 1 ≤ labelCount α a n := pow_pos halph a
  have hz : (labelCount α a n:ℝ)+1 ≤ 2*labelCount α a n := by
    have hz' : 1 ≤ (labelCount α a n:ℝ) := by exact_mod_cast hzpos
    linarith only [hz']
  have hz6 := pow_le_pow_left₀ (by positivity : 0 ≤ (labelCount α a n:ℝ)+1) hz 6
  rw [mul_pow] at hz6
  calc
    _ = (K:ℝ)*((cells:ℝ)+1)*((degree:ℝ)+1)*((labelCount α a n:ℝ)+1)^6 := by
      simp [scanEnvelope]
    _ ≤ K*((B+1)*r*(n:ℝ)^(9/10:ℝ))*(2*(n:ℝ)^(1/100:ℝ))*(2^6*(n:ℝ)^(4*α*a*(6:ℕ))) := by
      gcongr
      exact hz6.trans (mul_le_mul_of_nonneg_left hZ (by positivity))
    _ = r*(C*(n:ℝ)^e) := by dsimp [e,C]; rw [Real.rpow_add npos,Real.rpow_add npos]; ring
    _ < r*((C+1)*(n:ℝ)^e) := by gcongr; exact lt_add_one _
    _ ≤ _ := mul_le_mul_of_nonneg_left hC rpos.le

/-- The chosen team word width can hold any fixed polynomial in the address scale,
uniformly over all team sizes. -/
theorem eventually_polynomial_word (d : ℕ) : ∀ᶠ n : ℕ in atTop, ∀ r w : ℕ, 1 ≤ r →
    logWidth r n ^ 2 ≤ w → (2*n*r)^d < 2^w := by
  filter_upwards [eventually_ge_atTop (2^(d+1))] with n hn
  intro r w hr hw
  have hex : logWidth r n = Nat.clog 2 (2*n*r) := by
    unfold logWidth; rw [← Real.natCeil_logb_natCast]; norm_cast
  have hm : n ≤ 2*n*r := (by omega : n ≤ 2*n).trans (Nat.le_mul_of_pos_right _ hr)
  have hx : 2*n*r ≤ 2^logWidth r n := by rw [hex]; exact Nat.le_pow_clog (by decide) _
  have hd : d < logWidth r n := by
    have he := (hn.trans hm).trans hx
    exact Nat.lt_of_succ_le ((pow_le_pow_iff_right₀ (by decide : 1 < (2:ℕ))).mp he)
  calc
    _ ≤ (2^logWidth r n)^d := Nat.pow_le_pow_left hx _
    _ = 2^(logWidth r n*d) := (pow_mul ..).symm
    _ < 2^(logWidth r n^2) := by rw [sq]; exact Nat.pow_lt_pow_right (by decide) (Nat.mul_lt_mul_of_pos_left hd (by omega))
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hw

/-- All ordinary natural operands of the label score and any polynomial base address fit a
single permitted team word. The bound includes every directed bin and every data bin. -/
theorem eventually_label_word {α ξ : ℝ} (hα : 0 < α) (a : ℕ) (small : α*a < 1/10^6)
    (hξ : 0 ≤ ξ) (K d : ℕ) : ∀ᶠ n : ℕ in atTop, ∀ r R w base : ℕ, 1 ≤ r → R ≤ n →
    logWidth r n^2 ≤ w → base ≤ (2*n*r)^d →
    let W := exterior ξ r n*R
    let Z := labelCount α a n
    base + K*(W+1)^2*(Z+1)^6 < 2^w := by
  filter_upwards [eventually_labelCount_power hα a 1, eventually_polynomial_word (max d 11 + 1),
    eventually_ge_atTop (max K 1)] with n hZ word hn
  intro r R w base hr hR hw hb W Z
  have hn' : 1 ≤ n := (le_max_right ..).trans hn
  have hone : 1 ≤ (n:ℝ) := by exact_mod_cast hn'
  have hlabel : Z ≤ n := by
    have h := hZ.trans (Real.rpow_le_rpow_of_exponent_le hone (show 4*α*a*(1:ℕ) ≤ 1 by norm_num only [Nat.cast_one,mul_one]; linarith only [small]))
    simpa using h
  have hfloor : width n (1-ξ) ≤ n := by
    apply Nat.floor_le_of_le
    simpa using (Real.rpow_le_rpow_of_exponent_le hone (show 1-ξ ≤ 1 by linarith only [hξ]))
  let x := 2*n*r
  have hrn : 1 ≤ n*r := Nat.mul_pos hn' hr
  have hnr : n ≤ n*r := Nat.le_mul_of_pos_right n hr
  have hx : 2 ≤ x := by dsimp [x]; rw [Nat.mul_assoc]; omega
  have hW : W+1 ≤ x^2 := by
    have h : W ≤ (n*r)*n := by dsimp [W,exterior]; calc
      r*width n (1-ξ)*R ≤ r*n*n := by gcongr
      _ = _ := by ring
    have hh := (Nat.mul_le_mul_left (n*r) hnr)
    dsimp [x]; rw [Nat.mul_assoc 2 n r,sq]; nlinarith only [h,hh,hrn,pow_pos (show 0 < n*r from hrn) 2]
  have hZx : Z+1 ≤ x := by dsimp [x]; rw [Nat.mul_assoc]; omega
  have hk : K ≤ x := by have := (le_max_left K 1).trans hn; dsimp [x]; rw [Nat.mul_assoc]; omega
  have hcalc : K*(W+1)^2*(Z+1)^6 ≤ x^11 := calc
    _ ≤ x*(x^2)^2*x^6 := by gcongr
    _ = _ := by ring
  have hxd := Nat.pow_le_pow_right (by omega : 0 < x) (le_max_left d 11)
  have hxv := Nat.pow_le_pow_right (by omega : 0 < x) (le_max_right d 11)
  calc
    _ ≤ x^(max d 11)+x^(max d 11) := Nat.add_le_add (hb.trans hxd) (hcalc.trans hxv)
    _ ≤ x^(max d 11+1) := by rw [pow_succ,← Nat.mul_two]; exact Nat.mul_le_mul_left _ hx
    _ < _ := word r w hr hw

end Cube.MeanChoice

end BorderVNP
end Computability
end OAI

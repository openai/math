import OAI.Geometry.Hirsch.Valid

noncomputable section

open Filter

namespace OAI.Geometry.Hirsch.Layer

def Dials.count (u : Dials) := (2^u.h * (u.J+1))^u.h

namespace Growth.Plan

variable (p : Plan)

theorem count : ∀ᶠ r : ℕ in atTop, 2*((p.dial r).count : ℝ) ≤ E r 1 := by
  let x := 1/((p.h : ℝ)+1)
  have pos : 0 < x := by unfold x; positivity
  have gap : x*p.h < 1 := by
    unfold x; rw [div_mul_eq_mul_div,div_lt_one (by positivity)]; linarith
  have h := ((Order.identity x pos).scale 4).add ((Order.const 3).up pos.le)
  have hh := (((h.scale (2^p.h)).power p.h).scale 2).lt gap
  filter_upwards [hh] with r hr
  simp only [Dials.count,dial,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
  rw [show (4 : ℝ)*r+2+1 = 4*r+3 by ring]; exact hr.le

theorem bits : ∀ᶠ r : ℕ in atTop, 4*(r*p.h) ≤ 2^r := by
  have h := ((Order.identity (1/2) (by norm_num)).scale (4*p.h)).lt (y := 1) (by norm_num)
  filter_upwards [h] with r hr
  rw [one] at hr
  exact_mod_cast (show (4 : ℝ)*(r*p.h) ≤ 2^r by linarith)

def forMoves (m : ℕ) (hm : 0 < m) : Plan := ⟨64*m,32*exponent (64*m)*m,by omega⟩

theorem final_rate {m : ℕ} (hm : 0 < m) (r : ℕ) :
    let p := forMoves m hm
    (p.dial r).rate p.h = E r (-4*p.T) := by
  let p := forMoves m hm
  have he : (p.h : ℝ) = 32*p.T*m := by simp [p,forMoves,T]
  have hk : (p.K : ℝ) = 64*m := by simp [p,forMoves]
  have hpos : (m : ℝ) ≠ 0 := by positivity
  change E r (-2*p.T)*E r (-4/p.K)^p.h = E r (-4*p.T)
  rw [pow,mul,he,hk]; congr 1; field_simp; ring

end Growth.Plan

theorem Dials.choose (m : ℕ) (hm : 0 < m) :
    ∃ (u : Dials) (b bits chance : ℕ), u.Valid ∧ 2 ≤ b ∧ 0 < bits ∧ 0 < chance ∧
      b^m = u.a^u.h ∧ b^m ≤ 2^bits ∧ (2*chance)*(bits*2) ≤ b ∧
      2*(u.count : ℝ) ≤ chance*u.gamma*(u.rate u.h)^2 := by
  let p := Growth.Plan.forMoves m hm
  obtain ⟨r,hr,hv,hc,hbits⟩ := ((eventually_gt_atTop 0).and (p.valid.and (p.count.and p.bits))).exists
  let u := p.dial r
  have hT : 0 < p.T := by unfold Growth.Plan.T Growth.exponent; omega
  have hh : p.h = 32*p.T*m := rfl
  have he : ((2^r)^(32*p.T))^m = (2^r)^p.h := by rw [hh,pow_mul (2^r) (32*p.T) m]
  refine ⟨u,(2^r)^(32*p.T),r*p.h,(2^r)^(12*p.T),hv,?_,by rw [hh]; positivity,by positivity,he,?_,?_,?_⟩
  · exact (Nat.le_self_pow hr.ne' 2).trans (Nat.le_self_pow (by omega) _)
  · rw [he,pow_mul]
  · calc
      _ = (2^r)^(12*p.T)*(4*(r*p.h)) := by ring
      _ ≤ (2^r)^(12*p.T)*2^r := Nat.mul_le_mul_left _ hbits
      _ ≤ _ := by rw [← pow_succ]; exact Nat.pow_le_pow_right (by positivity) (by omega)
  · apply hc.trans
    change Growth.E r 1 ≤ (((2^r)^(12*p.T) : ℕ) : ℝ)*Growth.E r (-1)*((p.dial r).rate p.h)^2
    rw [Growth.Plan.final_rate hm r,Growth.nat,Growth.pow,Growth.mul,Growth.mul]
    apply Growth.mono
    change 1 ≤ (↑(12*p.T) : ℝ) + -1 + -4*p.T*↑(2 : ℕ)
    push_cast
    linarith [p.two,p.large]

end OAI.Geometry.Hirsch.Layer

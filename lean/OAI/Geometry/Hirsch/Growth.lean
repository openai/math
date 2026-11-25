import OAI.Geometry.Hirsch.Stages

noncomputable section

open Filter

namespace OAI.Geometry.Hirsch.Layer.Growth

def E (r : ℕ) (x : ℝ) := Real.exp ((r : ℝ)*Real.log 2*x)

theorem pos (r : ℕ) (x : ℝ) : 0 < E r x := Real.exp_pos _

theorem zero (r : ℕ) : E r 0 = 1 := by simp [E]

theorem one (r : ℕ) : E r 1 = (2 : ℝ)^r := by
  rw [E,mul_one,Real.exp_nat_mul,Real.exp_log (by norm_num)]

theorem mul (r : ℕ) (x y : ℝ) : E r x * E r y = E r (x+y) := by
  unfold E; rw [← Real.exp_add,mul_add]

theorem pow (r : ℕ) (x : ℝ) (k : ℕ) : E r x ^ k = E r (x*k) := by
  unfold E; rw [← Real.exp_nat_mul]; congr 1; ring

theorem nat (r k : ℕ) : (((2^r)^k : ℕ) : ℝ) = E r k := by
  rw [Nat.cast_pow,Nat.cast_pow,Nat.cast_ofNat,← one,pow,one_mul]

theorem mono (r : ℕ) {x y : ℝ} (h : x ≤ y) : E r x ≤ E r y := by
  unfold E; gcongr

theorem le_one (r : ℕ) {x : ℝ} (h : x ≤ 0) : E r x ≤ 1 := (mono r h).trans_eq (zero r)

theorem dominates {x y : ℝ} (h : x < y) (c : ℝ) :
    ∀ᶠ r : ℕ in atTop, c * E r x < E r y := by
  have logpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have gt : 1 < Real.exp (Real.log 2*(y-x)) := Real.one_lt_exp_iff.mpr (mul_pos logpos (sub_pos.mpr h))
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt gt).eventually (eventually_gt_atTop c)] with r hr
  rw [← Real.exp_nat_mul,← mul_assoc] at hr
  exact (mul_lt_mul_of_pos_right hr (pos r x)).trans_eq ((mul r (y-x) x).trans (by rw [sub_add_cancel]))

def Order (f : ℕ → ℝ) (x : ℝ) := ∃ c : ℝ, 0 < c ∧ ∀ᶠ r in atTop, |f r| ≤ c*E r x

namespace Order

variable {f g : ℕ → ℝ} {x y : ℝ}

theorem base (x : ℝ) : Order (fun r => E r x) x :=
  ⟨1,one_pos,Eventually.of_forall (fun r => by simp [abs_of_pos (pos r x)])⟩

theorem const (c : ℝ) : Order (fun _ => c) 0 :=
  ⟨|c|+1,by positivity,Eventually.of_forall (fun r => by simp [zero])⟩

theorem up (h : Order f x) (hh : x ≤ y) : Order f y := by
  obtain ⟨c,hc,h⟩ := h
  exact ⟨c,hc,h.mono fun r hr => hr.trans (mul_le_mul_of_nonneg_left (mono r hh) hc.le)⟩

theorem prod (h : Order f x) (hh : Order g y) : Order (fun r => f r*g r) (x+y) := by
  obtain ⟨c,hc,h⟩ := h
  obtain ⟨d,hd,hh⟩ := hh
  refine ⟨c*d,mul_pos hc hd,?_⟩
  filter_upwards [h,hh] with r hr hr'
  rw [abs_mul,← mul,mul_mul_mul_comm]
  exact mul_le_mul hr hr' (abs_nonneg _) (mul_nonneg hc.le (pos r x).le)

theorem scale (h : Order f x) (c : ℝ) : Order (fun r => c*f r) x :=
  ((const c).prod h).up (by simp)

theorem add (h : Order f x) (hh : Order g x) : Order (fun r => f r+g r) x := by
  obtain ⟨c,hc,h⟩ := h
  obtain ⟨d,hd,hh⟩ := hh
  refine ⟨c+d,add_pos hc hd,?_⟩
  filter_upwards [h,hh] with r hr hr'
  rw [add_mul]; exact (abs_add_le ..).trans (add_le_add hr hr')

theorem power (h : Order f x) (k : ℕ) : Order (fun r => f r^k) (x*k) := by
  obtain ⟨c,hc,h⟩ := h
  refine ⟨c^k,pow_pos hc _,?_⟩
  filter_upwards [h] with r hr
  rw [abs_pow,← pow,← mul_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hr _

theorem lt (h : Order f x) (hh : x < y) : ∀ᶠ r : ℕ in atTop, f r < E r y := by
  obtain ⟨c,_,h⟩ := h
  filter_upwards [h,dominates hh c] with r hr hr'
  exact ((le_abs_self _).trans hr).trans_lt hr'

theorem identity (x : ℝ) (hx : 0 < x) : Order (fun r => (r : ℝ)) x := by
  have h : 0 < Real.log 2*x := mul_pos (Real.log_pos (by norm_num)) hx
  refine ⟨(Real.log 2*x)⁻¹,inv_pos.mpr h,Eventually.of_forall fun r => ?_⟩
  rw [abs_of_nonneg (Nat.cast_nonneg _),inv_mul_eq_div,le_div_iff₀ h]
  unfold E; rw [mul_assoc]
  linarith [Real.add_one_le_exp ((r : ℝ)*(Real.log 2*x))]

end Order

def thresholds (K r : ℕ) (F : ℝ) (hF : 0 ≤ F) : Thresholds K where
  value j := E r (-F*3^(K-j))
  positive _ := pos ..
  mono := by
    intro i j hij
    apply mono
    apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hF)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  ratio := by
    intro j hj
    rw [pow,mul]
    apply mono
    rw [show K-j = K-(j+1)+1 by omega,pow_succ,Nat.sub_self,pow_zero]
    have := mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3) (n := K-(j+1))) hF
    push_cast
    linarith

end OAI.Geometry.Hirsch.Layer.Growth

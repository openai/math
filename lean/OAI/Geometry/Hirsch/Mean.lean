import OAI.Geometry.Hirsch.Primary

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Law

variable {Ω I : Type} [Fintype Ω] (p : Law Ω)

def mean (f : Ω → ℝ) := ∑ x, p.mass x * f x

def ind (a : Prop) : ℝ := if a then 1 else 0

theorem ind_nonneg (a : Prop) : 0 ≤ ind a := by unfold ind; split <;> norm_num

@[simp] theorem ind_mul (a b : Prop) : ind a * ind b = ind (a ∧ b) := by
  by_cases h : a <;> simp [ind,h]

@[simp] theorem ind_sq (a : Prop) : ind a ^ 2 = ind a := by rw [pow_two,ind_mul,and_self]

theorem mean_mono {f g : Ω → ℝ} (hh : ∀ x, f x ≤ g x) : p.mean f ≤ p.mean g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hh x) (p.nonneg x))

theorem mean_congr {f g : Ω → ℝ} (hh : ∀ x, f x = g x) : p.mean f = p.mean g := congrArg p.mean (funext hh)

theorem eq_prob {e f : Ω → Prop} (hh : ∀ x, e x ↔ f x) : p.prob e = p.prob f :=
  congrArg p.prob (funext fun x => propext (hh x))

@[simp] theorem mean_ind (e : Ω → Prop) : p.mean (fun x => ind (e x)) = p.prob e := by
  simp [mean,ind,prob,mul_ite]

@[simp] theorem mean_const (a : ℝ) : p.mean (fun _ => a) = a := by simp [mean,← Finset.sum_mul,p.total]

theorem mean_add (f g : Ω → ℝ) : p.mean (fun x => f x + g x) = p.mean f + p.mean g := by
  simp [mean,mul_add,Finset.sum_add_distrib]

theorem mean_scale (a : ℝ) (f : Ω → ℝ) : p.mean (fun x => a * f x) = a * p.mean f := by
  simp [mean,mul_left_comm,Finset.mul_sum]

theorem mean_sum (s : Finset I) (f : I → Ω → ℝ) :
    p.mean (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, p.mean (f i) := by
  simp only [mean,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem mean_comm (f : Ω → Ω → ℝ) : p.mean (fun x => p.mean (f x)) = p.mean (fun y => p.mean (fun x => f x y)) := by
  simp only [mean,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_left_comm]

theorem mean_kernel (a : Ω → ℝ) (f : Ω → Ω → ℝ) :
    p.mean (fun y => a y * p.mean (fun x => f x y)) = p.mean (fun x => p.mean (fun y => a y * f x y)) := by
  rw [p.mean_comm (fun x y => a y * f x y)]
  simp only [mean_scale]

theorem restricted_le {e : Ω → Prop} {f : Ω → ℝ} {a : ℝ} (hh : ∀ x, e x → f x ≤ a) :
    p.mean (fun x => ind (e x) * f x) ≤ a * p.prob e := by
  rw [← mean_ind,← mean_scale]
  exact p.mean_mono fun x => by by_cases h : e x <;> simp [ind,h,hh]

theorem restricted_ge {e : Ω → Prop} {f : Ω → ℝ} {a : ℝ} (hh : ∀ x, e x → a ≤ f x) :
    a * p.prob e ≤ p.mean (fun x => ind (e x) * f x) := by
  rw [← mean_ind,← mean_scale]
  exact p.mean_mono fun x => by by_cases h : e x <;> simp [ind,h,hh]

theorem transfer (bad e : Ω → Prop) (kernel : Ω → Ω → ℝ) {u C : ℝ} (hu : 0 < u) (hc : 0 < C)
    (lower : ∀ x, bad x → u ≤ p.mean (fun y => ind (e y)*kernel x y))
    (upper : ∀ x, bad x → p.mean (fun z => ind (bad z)*p.mean (fun y => kernel x y*kernel z y)) ≤ C) :
    u^2 * p.prob bad ≤ C * p.prob e := by
  let F := fun y => p.mean (fun x => ind (bad x)*kernel x y)
  have aux : ∀ a : Ω → ℝ, p.mean (fun y => a y * F y) =
      p.mean (fun x => ind (bad x) * p.mean (fun y => a y * kernel x y)) := by
    intro a
    unfold F
    rw [mean_kernel]
    apply p.mean_congr; intro x
    rw [← mean_scale]
    exact p.mean_congr (fun _ => by ring)
  have h₁ : u * p.prob bad ≤ p.mean (fun y => ind (e y) * F y) := by
    rw [aux]; exact p.restricted_ge lower
  have h₂ : p.mean (fun y => F y * F y) ≤ C * p.prob bad := by
    rw [aux]
    apply p.restricted_le
    intro x hx
    simp_rw [mul_comm (F _) (kernel _ _)]
    rw [aux]
    exact upper x hx
  have hb := p.mean_mono (fun y => show 2*u*C*(ind (e y)*F y) ≤ u^2*(F y*F y) + C^2*ind (e y) by
    by_cases he : e y <;> simp only [ind,he,↓reduceIte] <;> nlinarith [sq_nonneg (u*F y-C),sq_nonneg (u*F y)])
  rw [mean_scale,mean_add,mean_scale,mean_scale,mean_ind] at hb
  apply le_of_mul_le_mul_left _ hc
  linarith [mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 2*u*C by positivity),
    mul_le_mul_of_nonneg_left h₂ (sq_nonneg u)]

end OAI.Geometry.Hirsch.Layer.Law

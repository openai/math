import OAI.Geometry.Hirsch.Mean

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

variable {Ω I : Type} [Fintype Ω] [DecidableEq I]

structure Pins (p : Law Ω) (I : Type) where
  rate : ℝ
  pos : 0 < rate
  success : Ω → Finset I
  prob : ∀ s : Finset I, p.prob (fun x => s ⊆ success x) = rate^s.card

namespace Pins

open Law

variable {p : Law Ω} (pins : Pins p I)

def weight (s : Finset I) := pins.rate^s.card

omit [DecidableEq I] in
theorem positive (s : Finset I) : 0 < pins.weight s := pow_pos pins.pos _

theorem weight_union {s t : Finset I} (hd : Disjoint s t) :
    pins.weight (s ∪ t) = pins.weight s * pins.weight t := by
  simp [weight,Finset.card_union_of_disjoint hd,pow_add]

theorem weight_inter (s t : Finset I) :
    pins.weight (s ∪ t) * pins.weight (s ∩ t) = pins.weight s * pins.weight t := by
  simp [weight,← pow_add,Finset.card_union_add_card_inter]

def joint (e : Ω → Prop) (s : Finset I) := p.prob (fun x => e x ∧ s ⊆ pins.success x)

def given (e : Ω → Prop) (s : Finset I) := pins.joint e s / pins.weight s

def density (s : Finset I) (x : Ω) := (pins.weight s)⁻¹ * ind (s ⊆ pins.success x)

omit [DecidableEq I] in
theorem resolve (e : Ω → Prop) (s : Finset I) :
    p.mean (fun x => ind (e x) * pins.density s x) = pins.given e s := by
  simp_rw [density,mul_left_comm (ind _) (pins.weight s)⁻¹,ind_mul]
  rw [mean_scale,mean_ind,inv_mul_eq_div]; rfl

theorem overlap (s t : Finset I) : p.mean (fun x => pins.density s x * pins.density t x) =
    (pins.weight (s ∩ t))⁻¹ := by
  have he : ∀ x, pins.density s x * pins.density t x =
      (pins.weight s * pins.weight t)⁻¹ * ind (s ∪ t ⊆ pins.success x) := by
    intro x
    simp only [density,Finset.union_subset_iff,← ind_mul,mul_inv_rev]
    ring
  rw [p.mean_congr he,mean_scale,mean_ind,pins.prob,← pins.weight_inter]
  change (_ * _)⁻¹ * pins.weight (s ∪ t) = _
  rw [mul_inv_rev,mul_assoc,inv_mul_cancel₀ (pins.positive _).ne',mul_one]

theorem cross {P S : Finset I} (sub : S ⊆ P) {bad : Ω → Prop} {more : Ω → Finset I}
    (present : ∀ x, bad x → P ∪ more x ⊆ pins.success x) {R : Finset I} (hr : Disjoint P R) :
    p.mean (fun z => ind (bad z) * p.mean (fun y =>
      pins.density (S ∪ R) y * pins.density (S ∪ more z) y)) ≤
        (2 : ℝ)^R.card * (pins.weight P / pins.weight S) := by
  let f := fun J z => (pins.weight (S ∪ J))⁻¹ * ind (P ∪ J ⊆ pins.success z)
  have hn : ∀ J z, 0 ≤ f J z := fun J z => mul_nonneg (inv_nonneg.mpr (pins.positive _).le) (ind_nonneg _)
  have bound : ∀ z, ind (bad z) * p.mean (fun y =>
      pins.density (S ∪ R) y * pins.density (S ∪ more z) y) ≤ ∑ J ∈ R.powerset, f J z := by
    intro z
    by_cases hz : bad z
    swap
    · simp only [ind,hz,↓reduceIte,zero_mul]
      exact Finset.sum_nonneg (fun J _ => hn J z)
    let J := R ∩ more z
    have he : (S ∪ R) ∩ (S ∪ more z) = S ∪ J := by ext; simp [J]; tauto
    have hj : P ∪ J ⊆ pins.success z :=
      (Finset.union_subset_union_right Finset.inter_subset_right).trans (present z hz)
    have hmem : J ∈ R.powerset := Finset.mem_powerset.mpr Finset.inter_subset_left
    apply le_trans _ (Finset.single_le_sum (fun j _ => hn j z) hmem)
    rw [pins.overlap,he]
    simp [f,ind,hz,hj]
  have value : ∀ J ∈ R.powerset, p.mean (f J) = pins.weight P / pins.weight S := by
    intro J hJ
    have hd := hr.mono_right (Finset.mem_powerset.mp hJ)
    simp only [f,mean_scale,mean_ind,pins.prob]
    change (pins.weight (S ∪ J))⁻¹ * pins.weight (P ∪ J) = _
    rw [pins.weight_union hd,pins.weight_union (hd.mono_left sub),inv_mul_eq_div,
      mul_div_mul_right _ _ (pins.positive J).ne']
  apply (p.mean_mono bound).trans_eq
  rw [mean_sum,Finset.sum_congr rfl value]
  simp

theorem conditional_tail {P S : Finset I} (sub : S ⊆ P) (e : Ω → Prop) (K : ℕ) {u : ℝ} (hu : 0 < u) :
    u^2 * pins.given (fun x => ∃ R : Finset I, Disjoint P R ∧ R.card ≤ K ∧ R ⊆ pins.success x ∧
      u ≤ pins.given e (S ∪ R)) P ≤ (2 : ℝ)^K * pins.given e S := by
  let success := fun x (R : Finset I) => Disjoint P R ∧ R.card ≤ K ∧ R ⊆ pins.success x ∧
    u ≤ pins.given e (S ∪ R)
  let bad := fun x => (∃ R, success x R) ∧ P ⊆ pins.success x
  have hex : ∀ x, ∃ R, bad x → success x R := by
    intro x
    by_cases hx : bad x
    · obtain ⟨R,hR⟩ := hx.1; exact ⟨R,fun _ => hR⟩
    · exact ⟨∅,fun h => (hx h).elim⟩
  choose R hR using hex
  let C := (2 : ℝ)^K * (pins.weight P / pins.weight S)
  have hr := div_pos (pins.positive P) (pins.positive S)
  have hc : 0 < C := mul_pos (by positivity) hr
  have test := p.transfer bad (fun y => e y ∧ S ⊆ pins.success y)
    (fun x => pins.density (S ∪ R x)) hu hc
  have h : u^2 * p.prob bad ≤ C * pins.joint e S := by
    apply test
    · intro x hx
      apply (hR _ hx).2.2.2.trans_eq
      rw [← pins.resolve]
      apply p.mean_congr
      intro y
      by_cases hy : S ⊆ pins.success y
      · simp [hy]
      · simp [density,ind,Finset.union_subset_iff,hy]
    · intro x hx
      apply (pins.cross sub (fun z hz => Finset.union_subset hz.2 (hR z hz).2.2.1) (hR x hx).1).trans
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (hR x hx).2.1) hr.le
  change u^2 * (p.prob bad / pins.weight P) ≤ (2 : ℝ)^K * (pins.joint e S / pins.weight S)
  rw [← mul_div_assoc,div_le_iff₀ (pins.positive P)]
  exact h.trans_eq (by unfold C; ring)

end Pins
end OAI.Geometry.Hirsch.Layer

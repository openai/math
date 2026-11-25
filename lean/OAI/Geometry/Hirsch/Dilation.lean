import OAI.Geometry.Hirsch.StateVertex

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

variable {V : ℕ}

def replace (M : ℝ) (c : Values V) (mask : Fin V → Bool) : Values V :=
  fun l => if mask l then M else c l

def dilation (M : ℝ) (z : Values V) := 1 + M * ∑ l, max (-z l) 0

def scaled (M : ℝ) (z : Values V) : Values V := fun l => max (z l) 0 / dilation M z

def Expanded (cuts : Finset (Values V)) (M : ℝ) (z : Values V) : Prop :=
  ∀ c ∈ cuts, ∀ mask, 1 ≤ dot (replace M c mask) z

variable {M : ℝ} {c z : Values V}

theorem dilation_one (hm : 0 ≤ M) (z : Values V) : 1 ≤ dilation M z := by
  unfold dilation
  exact le_add_of_nonneg_right (mul_nonneg hm (Finset.sum_nonneg fun _ _ => le_max_right ..))

theorem dilation_two (hm : 0 ≤ M) {g : ℝ} (hg : 0 ≤ g) (hz : ∀ l, -g ≤ z l)
    (hh : M * (V * g) ≤ 1) : dilation M z ≤ 2 := by
  have hs : ∑ l, max (-z l) 0 ≤ V * g := by
    calc
      _ ≤ ∑ _ : Fin V, g := Finset.sum_le_sum fun l _ => max_le (neg_le.mp (hz l)) hg
      _ = _ := by simp
  unfold dilation
  linarith [mul_le_mul_of_nonneg_left hs hm]

theorem scaled_eq (hm : 0 ≤ M) (z : Values V) (l : Fin V) :
    scaled M z l * dilation M z = max (z l) 0 :=
  div_mul_cancel₀ _ (zero_lt_one.trans_le (dilation_one hm z)).ne'

theorem scaled_nonneg (hm : 0 ≤ M) (z : Values V) (l : Fin V) : 0 ≤ scaled M z l :=
  div_nonneg (le_max_right ..) (zero_le_one.trans (dilation_one hm z))

theorem scaled_large (hm : 0 ≤ M) {l : Fin V} {a : ℝ} (ha : 0 ≤ a) (hh : a < scaled M z l) :
    a < z l := by
  have := le_mul_of_one_le_right (scaled_nonneg hm z l) (dilation_one hm z)
  rw [scaled_eq hm] at this
  exact (lt_max_iff.mp (hh.trans_le this)).resolve_right ha.not_gt

theorem scaled_small (hm : 0 ≤ M) (hd : dilation M z ≤ 2) {l : Fin V} {a : ℝ}
    (hh : scaled M z l < a/2) : z l < a := by
  have := mul_le_mul_of_nonneg_left hd (scaled_nonneg hm z l)
  rw [scaled_eq hm] at this
  linarith [le_max_left (z l) 0]

def minimum (M : ℝ) (c z : Values V) (l : Fin V) := c l * max (z l) 0 - M * max (-z l) 0

theorem sum_minimum (hm : 0 ≤ M) (c z : Values V) :
    ∑ l, minimum M c z l = (dot c (scaled M z) - 1) * dilation M z + 1 := by
  have he : dot c (scaled M z) * dilation M z = ∑ l, c l * max (z l) 0 := by
    change (∑ l, c l * scaled M z l) * _ = _
    rw [Finset.sum_mul]
    simp only [mul_assoc,scaled_eq hm]
  rw [sub_mul,he,one_mul]
  simp only [minimum,dilation,Finset.sum_sub_distrib,Finset.mul_sum]
  ring

theorem minimum_le (hc : ∀ l, c l ≤ M) (mask : Fin V → Bool) (l : Fin V) :
    minimum M c z l ≤ replace M c mask l * z l := by
  unfold minimum replace
  rcases le_total 0 (z l) with hh | hh
  · rw [max_eq_left hh,max_eq_right (neg_nonpos.mpr hh),mul_zero,sub_zero]
    exact mul_le_mul_of_nonneg_right (by split <;> simp [hc]) hh
  · rw [max_eq_right hh,max_eq_left (neg_nonneg.mpr hh),mul_zero,zero_sub,mul_neg,neg_neg]
    exact mul_le_mul_of_nonpos_right (by split <;> simp [hc]) hh

theorem minimum_attained (M : ℝ) (c z : Values V) :
    ∃ mask, dot (replace M c mask) z = ∑ l, minimum M c z l := by
  refine ⟨fun l => decide (z l < 0),?_⟩
  change (∑ l, replace M c _ l * z l) = _
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hh : z l < 0
  · simp [replace,minimum,hh,hh.le]
  · simp [replace,minimum,hh,le_of_not_gt hh]

theorem expanded_iff {cuts : Finset (Values V)} (hm : 0 ≤ M) (hc : ∀ c ∈ cuts, ∀ l, c l ≤ M) :
    Expanded cuts M z ↔ scaled M z ∈ (region cuts).body := by
  have hd := zero_lt_one.trans_le (dilation_one hm z)
  rw [mem_region]
  constructor
  · intro hh
    refine ⟨scaled_nonneg hm z,fun c h => ?_⟩
    obtain ⟨mask,he⟩ := minimum_attained M c z
    have hv := hh c h mask
    rw [he,sum_minimum hm] at hv
    nlinarith
  · intro hh c h mask
    have hs : ∑ l, minimum M c z l ≤ dot (replace M c mask) z :=
      Finset.sum_le_sum fun l _ => minimum_le (hc c h) mask l
    rw [sum_minimum hm] at hs
    nlinarith [hh.2 c h]

theorem active_replacement (hm : 0 ≤ M) (hc : ∀ l, c l ≤ M) (mask : Fin V → Bool)
    (hv : 1 ≤ dot c (scaled M z)) (ha : dot (replace M c mask) z = 1) :
    dot c (scaled M z) = 1 ∧ ∀ l, 0 < z l → replace M c mask l = c l := by
  have hs : ∑ l, minimum M c z l ≤ dot (replace M c mask) z :=
    Finset.sum_le_sum fun l _ => minimum_le hc mask l
  have hd := dilation_one hm z
  rw [sum_minimum hm,ha] at hs
  have he : dot c (scaled M z) = 1 := by nlinarith
  refine ⟨he,fun l hl => ?_⟩
  have eqn : ∑ l, minimum M c z l = ∑ l, replace M c mask l * z l := by
    rw [sum_minimum hm,he,sub_self,zero_mul,zero_add]
    exact ha.symm
  have ht := (Finset.sum_eq_sum_iff_of_le (fun l _ => minimum_le hc mask l)).mp eqn l (Finset.mem_univ _)
  simp only [minimum,max_eq_left hl.le,max_eq_right (neg_nonpos.mpr hl.le),mul_zero,sub_zero] at ht
  exact mul_right_cancel₀ hl.ne' ht.symm

theorem expanded_pinned {cuts : Finset (Values V)} (hm : 0 ≤ M) (hc : ∀ c ∈ cuts, ∀ l, c l ≤ M)
    (hz : Expanded cuts M z) {tol : ℝ} (ht : 0 ≤ tol)
    (pin : ∀ dir : Values V, (∀ l, z l ≤ tol → dir l = 0) →
      (∀ c ∈ cuts, ∀ mask, dot (replace M c mask) z = 1 → dot (replace M c mask) dir = 0) →
      dir = 0) : Pinned cuts (scaled M z) tol := by
  intro dir hs ha
  have small : ∀ l, z l ≤ tol → dir l = 0 := fun l hl =>
    hs l (le_of_not_gt fun hh => hl.not_gt (scaled_large hm ht hh))
  apply pin dir small
  intro c hh mask he
  have hv := (mem_region.mp ((expanded_iff hm hc).mp hz)).2 c hh
  obtain ⟨he,hr⟩ := active_replacement hm (hc c hh) mask hv he
  rw [← ha c hh he]
  change (∑ l, replace M c mask l * dir l) = ∑ l, c l * dir l
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : 0 < z l
  · rw [hr l hl]
  · rw [small l ((le_of_not_gt hl).trans ht),mul_zero,mul_zero]

end OAI.Geometry.Hirsch.Layer

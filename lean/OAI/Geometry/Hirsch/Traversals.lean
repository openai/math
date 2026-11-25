import OAI.Geometry.Hirsch.Crossing

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

variable {a b lo hi : ℝ} {read : ℝ → ℝ}

theorem trim_forward (hc : Continuous read) (hab : a ≤ b)
    (hl : lo < hi) (ha : read a ≤ lo) (hb : hi ≤ read b) :
    ∃ s t, a ≤ s ∧ s < t ∧ t ≤ b ∧ read s = lo ∧ read t = hi ∧
      MapsTo read (Icc s t) (Icc lo hi) := by
  have compact : ∀ u v target : ℝ, IsCompact (Icc u v ∩ read ⁻¹' {target}) :=
    fun _ _ _ => isCompact_Icc.inter_right (isClosed_singleton.preimage hc)
  obtain ⟨early, he, heq⟩ := intermediate_value_Icc hab hc.continuousOn ⟨ha.trans hl.le, hb⟩
  obtain ⟨t, ⟨⟨hat, htb⟩, ht⟩, hmin⟩ := (compact a b hi).exists_isLeast ⟨early, he, heq⟩
  change read t = hi at ht
  obtain ⟨late, he', heq'⟩ := intermediate_value_Icc hat hc.continuousOn ⟨ha, ht ▸ hl.le⟩
  obtain ⟨s, ⟨⟨has, hst⟩, hs⟩, hmax⟩ := (compact a t lo).exists_isGreatest ⟨late, he', heq'⟩
  change read s = lo at hs
  refine ⟨s, t, has, lt_of_le_of_ne hst (by grind), htb, hs, ht, ?_⟩
  rintro u ⟨hsu, hut⟩
  constructor
  · by_contra! hn
    obtain ⟨v, ⟨huv, hvt⟩, hv⟩ := intermediate_value_Icc hut hc.continuousOn ⟨hn.le, ht ▸ hl.le⟩
    have hh := hmax ⟨⟨(has.trans hsu).trans huv, hvt⟩, hv⟩
    grind
  · by_contra! hn
    obtain ⟨v, ⟨hsv, hvu⟩, hv⟩ := intermediate_value_Icc hsu hc.continuousOn ⟨hs ▸ hl.le, hn.le⟩
    have hh := hmin ⟨⟨has.trans hsv, (hvu.trans hut).trans htb⟩, hv⟩
    grind

theorem trim (hc : Continuous read) (hab : a ≤ b) (hl : lo < hi)
    (hspan : Spans (read a) (read b) lo hi) :
    ∃ s t, a ≤ s ∧ s < t ∧ t ≤ b ∧
      ((read s = lo ∧ read t = hi) ∨ (read s = hi ∧ read t = lo)) ∧
      MapsTo read (Icc s t) (Icc lo hi) := by
  rcases le_total (read a) (read b) with hle | hle
  · rw [Spans, min_eq_left hle, max_eq_right hle] at hspan
    obtain ⟨s, t, hs, hst, ht, hf, hg, hm⟩ := trim_forward hc hab hl hspan.1 hspan.2
    exact ⟨s, t, hs, hst, ht, Or.inl ⟨hf, hg⟩, hm⟩
  · rw [Spans, min_eq_right hle, max_eq_left hle] at hspan
    obtain ⟨s, t, hs, hst, ht, hf, hg, hm⟩ := trim_forward hc.neg hab (neg_lt_neg hl)
      (neg_le_neg hspan.2) (neg_le_neg hspan.1)
    exact ⟨s, t, hs, hst, ht, Or.inr ⟨neg_inj.mp hf, neg_inj.mp hg⟩,
      fun u hu => ⟨neg_le_neg_iff.mp (hm hu).2, neg_le_neg_iff.mp (hm hu).1⟩⟩

def breaks (cuts : Finset ℝ) (a b : ℝ) := (cuts.filter (· ∈ Ioo a b)).card

theorem breaks_mono (cuts : Finset ℝ) {s t : ℝ} (hs : a ≤ s) (ht : t ≤ b) :
    breaks cuts s t ≤ breaks cuts a b := by
  apply Finset.card_le_card
  simp only [Finset.subset_iff, Finset.mem_filter, mem_Ioo]
  grind

theorem breaks_split (cuts : Finset ℝ) {u : ℝ} (hu : u ∈ Icc a b) :
    breaks cuts a u + breaks cuts u b ≤ breaks cuts a b := by
  unfold breaks
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    simp only [Finset.subset_iff, Finset.mem_union, Finset.mem_filter, mem_Ioo]
    grind
  · simp only [Finset.disjoint_left, Finset.mem_filter, mem_Ioo]
    grind

theorem breaks_split_lt (cuts : Finset ℝ) {u : ℝ} (hu : u ∈ Ioo a b) (hm : u ∈ cuts) :
    breaks cuts a u + breaks cuts u b < breaks cuts a b := by
  unfold breaks
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · simp only [Finset.subset_iff, Finset.mem_union, Finset.mem_filter, mem_Ioo]
      grind
    · intro he
      have hh := Finset.mem_filter.mpr ⟨hm, hu⟩
      rw [← he] at hh
      simp at hh
  · simp only [Finset.disjoint_left, Finset.mem_filter, mem_Ioo]
    grind

theorem count_traversals (cuts : Finset ℝ) (hc : Continuous read) (cost : ℕ)
    {count : ℕ} (left right : Fin count → ℝ) (hw : ∀ idx, left idx < right idx)
    (ho : ∀ first last, first < last → right first ≤ left last)
    (hab : a ≤ b) (hs : ∀ idx, Spans (read a) (read b) (left idx) (right idx))
    (hb : ∀ idx s t, a ≤ s → s ≤ t → t ≤ b →
      Spans (read s) (read t) (left idx) (right idx) → cost ≤ breaks cuts s t) :
    count * cost ≤ breaks cuts a b := by
  induction count generalizing a b with
  | zero => simp
  | succ count ih =>
    have hzero := hs 0
    have hwidth := hw 0
    have htail : ∀ idx : Fin count, right 0 ≤ left idx.succ := fun idx => ho _ _ (Fin.succ_pos idx)
    have hrest := fun first last (hh : first < last) =>
      ho (Fin.succ first) (Fin.succ last) (Fin.succ_lt_succ_iff.mpr hh)
    rcases le_total (read a) (read b) with hle | hle
    · obtain ⟨u, hu, he⟩ := intermediate_value_Icc hab hc.continuousOn
        (show right 0 ∈ Icc (read a) (read b) by unfold Spans at hzero; grind)
      have hf := hb 0 a u le_rfl hu.1 hu.2 (by unfold Spans at *; grind)
      have hl := ih (left ∘ Fin.succ) (right ∘ Fin.succ) (fun idx => hw _) hrest hu.2
        (by intro idx; have := hs idx.succ; have := htail idx; unfold Spans at *; simp only [Function.comp_apply]; grind)
        (fun idx s t hh => hb idx.succ s t (hu.1.trans hh))
      rw [Nat.succ_mul]
      have := breaks_split cuts hu
      omega
    · obtain ⟨u, hu, he⟩ := intermediate_value_Icc' hab hc.continuousOn
        (show right 0 ∈ Icc (read b) (read a) by unfold Spans at hzero; grind)
      have hf := hb 0 u b hu.1 hu.2 le_rfl (by unfold Spans at *; grind)
      have hl := ih (left ∘ Fin.succ) (right ∘ Fin.succ) (fun idx => hw _) hrest hu.1
        (by intro idx; have := hs idx.succ; have := htail idx; unfold Spans at *; simp only [Function.comp_apply]; grind)
        (fun idx s t hh hh' hh'' => hb idx.succ s t hh hh' (hh''.trans hu.2))
      rw [Nat.succ_mul]
      have := breaks_split cuts hu
      omega

end OAI.Geometry.Hirsch

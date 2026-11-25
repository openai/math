import OAI.Geometry.Hirsch.Traversals

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

variable {Space : Type} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  {region : Set Space} {a b : ℝ} {cuts : Finset ℝ} {path : ℝ → Space}

structure Broken (region : Set Space) (path : ℝ → Space) (cuts : Finset ℝ) (a b : ℝ) : Prop where
  continuous : Continuous path
  inside : MapsTo path (Icc a b) region
  chord : ∀ s t, a ≤ s → s ≤ t → t ≤ b → breaks cuts s t = 0 →
    segment ℝ (path s) (path t) ⊆ path '' Icc s t

theorem Broken.restrict (hp : Broken region path cuts a b) {s t : ℝ} (hs : a ≤ s) (ht : t ≤ b) :
    Broken region path cuts s t :=
  ⟨hp.continuous, fun _ hh => hp.inside ⟨hs.trans hh.1, hh.2.trans ht⟩,
    fun u v hu huv hv => hp.chord u v (hs.trans hu) huv (hv.trans ht)⟩

theorem Broken.segment_subset (hp : Broken region path cuts a b) (hab : a ≤ b) (hz : breaks cuts a b = 0) :
    segment ℝ (path a) (path b) ⊆ region :=
  (hp.chord a b le_rfl hab le_rfl hz).trans hp.inside.image_subset

def line (first last : Space) (stop t : ℝ) := (stop - t) • (first - last) + last

theorem line_start (first last : Space) (stop : ℝ) : line first last stop (stop - 1) = first := by
  simp [line]

theorem line_stop (first last : Space) (stop : ℝ) : line first last stop stop = last := by simp [line]

theorem broken_line {first last : Space} (hs : segment ℝ first last ⊆ region) (stop : ℝ) :
    Broken region (line first last stop) ∅ (stop - 1) stop := by
  constructor
  · unfold line; fun_prop
  · rintro t ⟨hl, hu⟩
    apply hs
    refine ⟨stop - t, 1 - (stop - t), by linarith, by linarith, by ring, ?_⟩
    unfold line
    module
  · rintro s t _ hst _ _ _ ⟨u, v, hu, hv, he, rfl⟩
    have hh : u • s + v • t ∈ Icc s t :=
      convex_Icc _ _ (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst) hu hv he
    refine ⟨_, hh, ?_⟩
    rw [show u = 1 - v by linarith]
    unfold line
    simp only [smul_eq_mul]
    module

theorem Broken.prepend (hp : Broken region path cuts a b) (hab : a ≤ b)
    {first : Space} (hs : segment ℝ first (path a) ⊆ region) :
    ∃ next, Broken region next (insert a cuts) (a - 1) b ∧ next (a - 1) = first ∧ next b = path b := by
  let head := line first (path a) a
  have hh := broken_line hs a
  let next := fun t => if t ≤ a then head t else path t
  have hl : ∀ t ≤ a, next t = head t := fun t ht => by simp [next, ht]
  have hr : ∀ t, a ≤ t → next t = path t := by
    intro t ht
    rcases ht.eq_or_lt with rfl | hlt
    · simp [next, head, line_stop]
    · simp [next, hlt.not_ge]
  refine ⟨next, ?_, (hl _ (by linarith)).trans (line_start _ _ _), hr _ hab⟩
  constructor
  · exact hh.continuous.if_le hp.continuous continuous_id continuous_const
      (fun t ht => by subst t; exact line_stop _ _ _)
  · rintro t ⟨ht, ht'⟩
    rcases le_total t a with he | he
    · rw [hl _ he]; exact hh.inside ⟨ht, he⟩
    · rw [hr _ he]; exact hp.inside ⟨he, ht'⟩
  · intro s t hstart hst hend hz
    have hempty : ∀ u ∈ insert a cuts, u ∉ Ioo s t := by
      simpa [breaks, Finset.filter_eq_empty_iff] using hz
    by_cases ht : t ≤ a
    · rw [hl _ (hst.trans ht), hl _ ht]
      rintro pt hpt
      obtain ⟨u, hu, he⟩ := hh.chord s t hstart hst ht (by simp [breaks]) hpt
      exact ⟨u, hu, (hl _ (hu.2.trans ht)).trans he⟩
    · have hs' : a ≤ s := by have := hempty a (Finset.mem_insert_self ..); grind
      have hz' : breaks cuts s t = 0 := by
        simp only [breaks, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        exact fun u hu => hempty u (Finset.mem_insert_of_mem hu)
      rw [hr _ hs', hr _ (hs'.trans hst)]
      rintro pt hpt
      obtain ⟨u, hu, he⟩ := hp.chord s t hs' hst hend hz' hpt
      exact ⟨u, hu, (hr _ (hs'.trans hu.1)).trans he⟩

theorem Segments.broken {len : ℕ} {pts : Fin (len + 1) → Space}
    (hs : Segments region pts) (hp : 0 < len) :
    ∃ path cuts a b, a ≤ b ∧ Broken region path cuts a b ∧
      path a = pts 0 ∧ path b = pts (Fin.last len) ∧ cuts.card < len := by
  induction len with
  | zero => omega
  | succ len ih =>
    have hf : segment ℝ (pts 0) (pts (Fin.succ 0)) ⊆ region := hs 0
    by_cases hz : len = 0
    · subst len
      exact ⟨_, ∅, 0 - 1, 0, by norm_num, broken_line hf 0,
        line_start _ _ _, line_stop _ _ _, by simp⟩
    have hh : Segments region (Fin.tail pts) := fun idx => hs idx.succ
    obtain ⟨path, cuts, a, b, hab, hb, hl, hr, hc⟩ := ih hh (by omega)
    obtain ⟨next, hn, hl', hr'⟩ := hb.prepend hab (first := pts 0) (by rw [hl]; exact hf)
    exact ⟨_, _, _, _, by linarith, hn, hl', hr'.trans hr,
      lt_of_le_of_lt (Finset.card_insert_le _ _) (Nat.succ_lt_succ hc)⟩

inductive Links (region : Set Space) : ℕ → Space → Space → Prop
  | nil (pt) : Links region 0 pt pt
  | cons {len first next last} (hs : segment ℝ first next ⊆ region)
      (tail : Links region len next last) : Links region (len + 1) first last

theorem Links.append {m n : ℕ} {first mid last : Space}
    (hf : Links region m first mid) (hl : Links region n mid last) :
    Links region (m + n) first last := by
  induction hf with
  | nil => simpa
  | cons hs _ ih => simpa [Nat.succ_add] using Links.cons hs (ih hl)

theorem Links.segments {len : ℕ} {first last : Space} (hh : Links region len first last) :
    ∃ pts : Fin (len + 1) → Space, Segments region pts ∧ pts 0 = first ∧ pts (Fin.last len) = last := by
  induction hh with
  | nil pt => exact ⟨fun _ => pt, fun idx => idx.elim0, rfl, rfl⟩
  | @cons len first next last hs _ ih =>
    obtain ⟨pts, hp, hl, hr⟩ := ih
    refine ⟨Fin.cons first pts, ?_, Fin.cons_zero .., by simpa using hr⟩
    refine Fin.cases ?_ (fun idx => ?_)
    · simpa [hl] using hs
    · simpa only [Fin.castSucc_succ, Fin.cons_succ] using hp idx

theorem links_of_breaks (factor : ℕ) (hab : a ≤ b)
    (hh : ∀ s t, a ≤ s → s ≤ t → t ≤ b → breaks cuts s t = 0 →
      ∃ len ≤ factor, Links region len (path s) (path t)) :
    ∃ len ≤ factor * (breaks cuts a b + 1), Links region len (path a) (path b) := by
  generalize he : breaks cuts a b = count
  induction count using Nat.strong_induction_on generalizing a b with
  | h count ih =>
    by_cases hz : count = 0
    · simpa [hz] using hh a b le_rfl hab le_rfl (he.trans hz)
    obtain ⟨mid, hm⟩ := Finset.card_pos.mp (show 0 < breaks cuts a b by omega)
    obtain ⟨hm, hu⟩ := Finset.mem_filter.mp hm
    have hl := breaks_split_lt cuts hu hm
    obtain ⟨m, hm', hf⟩ := ih (breaks cuts a mid) (by omega) hu.1.le
      (fun s t hs hst ht => hh s t hs hst (ht.trans hu.2.le)) rfl
    obtain ⟨n, hn, hg⟩ := ih (breaks cuts mid b) (by omega) hu.2.le
      (fun s t hs => hh s t (hu.1.le.trans hs)) rfl
    refine ⟨m + n, (Nat.add_le_add hm' hn).trans ?_, hf.append hg⟩
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (by omega)

end OAI.Geometry.Hirsch

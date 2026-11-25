import OAI.Geometry.Hirsch.Paths
import OAI.Geometry.Hirsch.Admissibility

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

variable {Coord : Type} [Fintype Coord] {region : Set (Timed Coord)}
  {path : ℝ → Timed Coord} {cuts : Finset ℝ} {a b lo hi : ℝ} {cost : ℕ}

theorem CrossingBound.links (hc : CrossingBound region lo hi cost)
    {len : ℕ} {first last : Timed Coord} (hl : Links region len first last)
    (hs : Spans first.1 last.1 lo hi) : cost ≤ len := by
  obtain ⟨pts, hp, he, he'⟩ := hl.segments
  exact hc _ _ hp (by rwa [he, he'])

theorem CrossingBound.breaks (hc : CrossingBound region lo hi (cost + 1))
    (hp : Broken region path cuts a b) (hab : a ≤ b) (hs : Spans (path a).1 (path b).1 lo hi) :
    cost ≤ OAI.Geometry.Hirsch.breaks cuts a b := by
  obtain ⟨len, hl, hh⟩ := links_of_breaks 1 hab (fun s t hs hst ht hz =>
    ⟨1, le_rfl, Links.cons ((hp.restrict hs ht).segment_subset hst hz) (Links.nil _)⟩)
  have he := hc.links hh hs
  omega

theorem crossing_of_breaks (hw : lo < hi)
    (hc : ∀ path cuts a b, Broken region path cuts a b → a ≤ b →
      Spans (path a).1 (path b).1 lo hi → cost ≤ breaks cuts a b) :
    CrossingBound region lo hi (cost + 1) := by
  intro len pts hs hspan
  have hpos : 0 < len := by
    by_contra! hn
    have he : Fin.last len = 0 := Fin.ext (by simpa using Nat.eq_zero_of_le_zero hn)
    simp [Spans, he] at hspan
    linarith
  obtain ⟨path, cuts, a, b, hab, hp, hl, hr, hn⟩ := hs.broken hpos
  have hh := hc path cuts a b hp hab (by rwa [hl, hr])
  have ht : breaks cuts a b ≤ cuts.card := Finset.card_filter_le _ _
  omega

theorem episodes_crossing {count : ℕ} (episodes : Episodes count)
    (hc : ∀ idx, CrossingBound region (episodes.left idx) (episodes.right idx) (cost + 1)) :
    CrossingBound region 0 1 (count * cost + 1) := by
  apply crossing_of_breaks zero_lt_one
  intro path cuts a b hp hab hs
  apply count_traversals cuts hp.continuous.fst cost episodes.left episodes.right episodes.width
    (fun _ _ hh => (episodes.ordered hh).le) hab
  · exact fun idx => ⟨hs.1.trans (episodes.positive idx).le, (episodes.interior idx).le.trans hs.2⟩
  · exact fun idx _ _ hl hle hr hh => (hc idx).breaks (hp.restrict hl hr) hle hh

def Transfer (region : Set (Timed Coord)) (read : Timed Coord → ℝ)
    (phase : Set ℝ) (lo hi : ℝ) (cost : ℕ) : Prop :=
  ∀ path cuts a b, Broken region path cuts a b → a ≤ b →
    MapsTo (fun t => (path t).1) (Icc a b) phase →
    Spans (read (path a)) (read (path b)) lo hi → cost ≤ breaks cuts a b

theorem transfer_of_chords {Inner : Type} [Fintype Inner] {inner : Set (Timed Inner)}
    {read : Timed Coord → ℝ} (hc : Continuous read) (image : Timed Coord → Timed Inner)
    {phase : Set ℝ} {left right : ℝ} (hw : left < right) (hl : lo ≤ left) (hr : right ≤ hi)
    (start : ∀ pt ∈ region, read pt = left → (image pt).1 = 0)
    (finish : ∀ pt ∈ region, read pt = right → (image pt).1 = 1)
    (chords : ∀ first last, (∀ pt ∈ segment ℝ first last, pt ∈ region ∧ pt.1 ∈ phase ∧
      read pt ∈ Icc left right) → ∃ len ≤ 2, Links inner len (image first) (image last))
    (bound : CrossingBound inner 0 1 (2 * cost + 1)) : Transfer region read phase lo hi cost := by
  intro path cuts a b hp hab hphase hspan
  obtain ⟨s, t, hs, hst, ht, hor, hm⟩ := trim (hc.comp hp.continuous) hab hw
    ⟨hspan.1.trans hl, hr.trans hspan.2⟩
  have hmap : ∀ u ∈ Icc s t, path u ∈ region ∧ (path u).1 ∈ phase ∧ read (path u) ∈ Icc left right := by
    intro u hu
    have hv := Icc_subset_Icc hs ht hu
    exact ⟨hp.inside hv, hphase hv, hm hu⟩
  obtain ⟨len, hlen, hlinks⟩ := links_of_breaks (path := image ∘ path) (cuts := cuts)
    (region := inner) 2 hst.le (by
      intro u v hu huv hv hz
      apply chords
      intro pt hpt
      obtain ⟨w, hh, rfl⟩ := hp.chord u v (hs.trans hu) huv (hv.trans ht) hz hpt
      exact hmap w (Icc_subset_Icc hu hv hh))
  have hf := (hmap s ⟨le_rfl, hst.le⟩).1
  have hg := (hmap t ⟨hst.le, le_rfl⟩).1
  have he := bound.links hlinks (by
    change Spans (image (path s)).1 (image (path t)).1 0 1
    rcases hor with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · simp [Spans, start _ hf hx, finish _ hg hy]
    · simp [Spans, finish _ hf hx, start _ hg hy])
  have := breaks_mono cuts hs ht
  omega

structure Phases where
  bandLeft : ℝ
  earlyEnd : ℝ
  lateStart : ℝ
  bandRight : ℝ
  early : bandLeft < earlyEnd
  ordered : earlyEnd < lateStart
  late : lateStart < bandRight

def Phases.overlapLeft (ph : Phases) (side : Bool) := if side then ph.lateStart else ph.bandLeft
def Phases.overlapRight (ph : Phases) (side : Bool) := if side then ph.bandRight else ph.earlyEnd

theorem Phases.alternative (ph : Phases) (time : ℝ → ℝ) (a b : ℝ) :
    MapsTo time (Icc a b) (Iic ph.earlyEnd) ∨ MapsTo time (Icc a b) (Ici ph.lateStart) ∨
    MapsTo time (Icc a b) (Icc ph.bandLeft ph.bandRight) ∨
    ∃ side u v, a ≤ u ∧ u ≤ v ∧ v ≤ b ∧
      Spans (time u) (time v) (ph.overlapLeft side) (ph.overlapRight side) := by
  have aux : ∀ side s t, s ∈ Icc a b → t ∈ Icc a b →
      time s ≤ ph.overlapLeft side → ph.overlapRight side ≤ time t →
      ∃ side u v, a ≤ u ∧ u ≤ v ∧ v ≤ b ∧
        Spans (time u) (time v) (ph.overlapLeft side) (ph.overlapRight side) := by
    intro side s t hs ht hl hr
    rcases le_total s t with hle | hle
    · exact ⟨side, s, t, hs.1, hle, ht.2, (min_le_left _ _).trans hl, hr.trans (le_max_right _ _)⟩
    · exact ⟨side, t, s, ht.1, hle, hs.2, (min_le_right _ _).trans hl, hr.trans (le_max_left _ _)⟩
  by_cases he : MapsTo time (Icc a b) (Iic ph.earlyEnd)
  · exact Or.inl he
  by_cases hl : MapsTo time (Icc a b) (Ici ph.lateStart)
  · exact Or.inr (Or.inl hl)
  by_cases hb : MapsTo time (Icc a b) (Icc ph.bandLeft ph.bandRight)
  · exact Or.inr (Or.inr (Or.inl hb))
  right; right; right
  simp only [MapsTo, mem_Iic, mem_Ici, mem_Icc, not_forall, not_le, not_and_or] at he hl hb
  obtain ⟨s, hs, hh | hh⟩ := hb
  · obtain ⟨t, ht, hv⟩ := he
    exact aux false s t hs ht hh.le hv.le
  · obtain ⟨t, ht, hv⟩ := hl
    exact aux true t s ht hs hv.le hh.le

structure Driver (region : Set (Timed Coord)) (lo hi : ℝ) (buckets windows cost : ℕ) where
  phase : Fin buckets → Phases
  contained : ∀ bucket, lo < (phase bucket).bandLeft ∧ (phase bucket).bandRight < hi
  read : Fin buckets → Timed Coord → ℝ
  continuous : ∀ bucket, Continuous (read bucket)
  work : Episodes windows
  anchors : ∀ first ∈ region, ∀ last ∈ region, first.1 = lo → last.1 = hi →
    ∃ bucket, ∀ idx, Spans (read bucket first) (read bucket last) (work.left idx) (work.right idx)
  early : ∀ bucket idx, Transfer region (read bucket) (Icc lo (phase bucket).earlyEnd)
    (work.left idx) (work.right idx) cost
  late : ∀ bucket idx, Transfer region (read bucket) (Icc (phase bucket).lateStart hi)
    (work.left idx) (work.right idx) cost
  band : ∀ bucket idx, Transfer region (read bucket) (Icc (phase bucket).bandLeft (phase bucket).bandRight)
    (work.left idx) (work.right idx) cost

theorem Driver.crossing {buckets windows inner : ℕ} (driver : Driver region lo hi buckets windows cost)
    (hw : lo < hi) (overlaps : ∀ bucket side, CrossingBound region
      ((driver.phase bucket).overlapLeft side) ((driver.phase bucket).overlapRight side) (inner + 1)) :
    CrossingBound region lo hi (windows * min cost inner + 1) := by
  apply crossing_of_breaks hw
  intro path cuts a b hp hab hs
  obtain ⟨s, t, hs, hst, ht, hor, hm⟩ := trim hp.continuous.fst hab hw hs
  have sub := hp.restrict hs ht
  have hf := sub.inside (left_mem_Icc.mpr hst.le)
  have hl := sub.inside (right_mem_Icc.mpr hst.le)
  have hex : ∃ bucket, ∀ idx, Spans (driver.read bucket (path s)) (driver.read bucket (path t))
      (driver.work.left idx) (driver.work.right idx) := by
    rcases hor with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact driver.anchors _ hf _ hl hx hy
    · obtain ⟨bucket, hh⟩ := driver.anchors _ hl _ hf hy hx
      exact ⟨bucket, fun idx => by simpa [Spans, min_comm, max_comm] using hh idx⟩
  obtain ⟨bucket, hh⟩ := hex
  apply le_trans _ (breaks_mono cuts hs ht)
  apply count_traversals cuts ((driver.continuous bucket).comp hp.continuous) _ _ _
    driver.work.width (fun _ _ h => (driver.work.ordered h).le) hst.le hh
  intro idx u v hu huv hv hspan
  have small := sub.restrict hu hv
  have time := hm.mono_left (Icc_subset_Icc hu hv)
  rcases (driver.phase bucket).alternative (fun t => (path t).1) u v with he | hl | hb | ho
  · exact (min_le_left _ _).trans (driver.early bucket idx _ _ _ _ small huv
      (fun _ h => ⟨(time h).1, he h⟩) hspan)
  · exact (min_le_left _ _).trans (driver.late bucket idx _ _ _ _ small huv
      (fun _ h => ⟨hl h, (time h).2⟩) hspan)
  · exact (min_le_left _ _).trans (driver.band bucket idx _ _ _ _ small huv hb hspan)
  · obtain ⟨side, x, y, hx, hxy, hy, he⟩ := ho
    exact (min_le_right _ _).trans (((overlaps bucket side).breaks (small.restrict hx hy) hxy he).trans
      (breaks_mono cuts hx hy))

end OAI.Geometry.Hirsch

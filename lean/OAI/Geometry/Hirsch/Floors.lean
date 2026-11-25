import OAI.Geometry.Hirsch.Straightening

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

namespace Episodes

variable {count : ℕ} (ep : Episodes count)

theorem gap_scale : ∃ scale > 0, ∀ first last, first < last →
    2 ≤ scale * (ep.left last - ep.right first) := by
  obtain ⟨val, hv⟩ := Finite.bddAbove_range
    (fun pair : Fin count × Fin count => 2 / (ep.left pair.2 - ep.right pair.1))
  exact ⟨max 1 val, zero_lt_one.trans_le (le_max_left ..), fun first last hh =>
    (div_le_iff₀ (sub_pos.mpr (ep.ordered hh))).mp
      ((hv (mem_range_self (first, last))).trans (le_max_right ..))⟩

def carrier (scale : ℝ) (idx : Fin count) (time : ℝ) :=
  ∑ pos : Fin count, if pos < idx then scale * (time - ep.right pos) - 1 else 0

theorem carrier_affine (scale : ℝ) (idx : Fin count) (time : ℝ) :
    (ep.carrier scale idx 1 - ep.carrier scale idx 0) * time + ep.carrier scale idx 0 =
      ep.carrier scale idx time := by
  unfold carrier
  rw [← Finset.sum_sub_distrib, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pos _
  split <;> ring

theorem carrier_dominates {scale : ℝ} (hs : 0 < scale)
    (hg : ∀ first last, first < last → 2 ≤ scale * (ep.left last - ep.right first))
    {idx other : Fin count} (hn : idx ≠ other) {time : ℝ} (ht : time ∈ Icc (ep.left idx) (ep.right idx)) :
    1 ≤ ep.carrier scale idx time - ep.carrier scale other time := by
  let val := fun pos => scale * (time - ep.right pos) - 1
  have hl : ∀ pos < idx, 1 ≤ val pos := by
    intro pos hp
    unfold val
    linarith [hg _ _ hp, mul_le_mul_of_nonneg_left ht.1 hs.le]
  have hr : ∀ pos, idx ≤ pos → val pos ≤ -1 := by
    intro pos hp
    have hh : time ≤ ep.right pos := by
      rcases hp.eq_or_lt with rfl | hh
      · exact ht.2
      · exact ht.2.trans ((ep.ordered hh).trans (ep.width pos)).le
    unfold val
    linarith [mul_nonpos_of_nonneg_of_nonpos hs.le (sub_nonpos.mpr hh)]
  let term := fun pos => (if pos < idx then val pos else 0) - (if pos < other then val pos else 0)
  have hh : ∀ pos, 0 ≤ term pos := by
    intro pos
    unfold term
    specialize hl pos
    specialize hr pos
    split <;> split <;> grind
  unfold carrier
  rw [← Finset.sum_sub_distrib]
  change 1 ≤ ∑ pos, term pos
  rcases lt_or_gt_of_ne hn with he | he
  · apply le_trans _ (Finset.single_le_sum (fun pos _ => hh pos) (Finset.mem_univ idx))
    simp [term, he]
    linarith [hr idx le_rfl]
  · apply le_trans _ (Finset.single_le_sum (fun pos _ => hh pos) (Finset.mem_univ other))
    simpa [term, he] using hl other he

end Episodes

namespace Phases

def ramp (ph : Phases) (side : Bool) (time : ℝ) :=
  (time - ph.earlyEnd) / (ph.lateStart - ph.earlyEnd) - if side then 1 else 0

theorem ramp_early (ph : Phases) {time : ℝ} (ht : time ≤ ph.earlyEnd) (side : Bool) :
    ph.ramp side time ≤ 0 := by
  have hh := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr ph.ordered.le)
  cases side <;> simp [ramp] <;> linarith

theorem ramp_late (ph : Phases) {time : ℝ} (ht : ph.lateStart ≤ time) (side : Bool) :
    0 ≤ ph.ramp side time := by
  have hh : 1 ≤ (time - ph.earlyEnd) / (ph.lateStart - ph.earlyEnd) :=
    (le_div_iff₀ (sub_pos.mpr ph.ordered)).mpr (by linarith)
  cases side <;> simp [ramp] <;> linarith

end Phases

variable {count buckets : ℕ} [NeZero count]

structure Floors (ep : Episodes count) (phase : Fin count → Fin buckets → Phases) where
  carrierScale : ℝ
  positive : 0 < carrierScale
  gaps : ∀ first last, first < last → 2 ≤ carrierScale * (ep.left last - ep.right first)
  rampBound : ℝ
  boundPos : 0 < rampBound
  bounded : ∀ idx bucket side time, time ∈ Icc (0 : ℝ) 1 → (phase idx bucket).ramp side time ≤ rampBound

namespace Floors

variable {ep : Episodes count} {phase : Fin count → Fin buckets → Phases}

omit [NeZero count] in
theorem exists_floors (ep : Episodes count) (phase : Fin count → Fin buckets → Phases) :
    Nonempty (Floors ep phase) := by
  obtain ⟨scale, hs, hg⟩ := ep.gap_scale
  obtain ⟨val, hv⟩ := Finite.bddAbove_range (fun pair : Fin count × Fin buckets =>
    (phase pair.1 pair.2).ramp false 1)
  refine ⟨⟨scale, hs, hg, max 1 val, zero_lt_one.trans_le (le_max_left ..), ?_⟩⟩
  intro idx bucket side time ht
  apply le_trans _ ((hv (mem_range_self (idx, bucket))).trans (le_max_right ..))
  have hh := div_le_div_of_nonneg_right (sub_le_sub_right ht.2 (phase idx bucket).earlyEnd)
    (sub_nonneg.mpr (phase idx bucket).ordered.le)
  cases side <;> simp [Phases.ramp] <;> linarith

variable (floors : Floors ep phase)

def base (idx : Fin count) (time : ℝ) := 1 + floors.rampBound * ep.carrier floors.carrierScale idx time

def piece (bucket : Fin buckets) (side : Bool) (pos : Fin count × Bool) (time : ℝ) :=
  floors.base pos.1 time + if pos.2 then (phase pos.1 bucket).ramp side time else 0

omit [NeZero count] in
theorem affine (bucket side pos time) :
    (floors.piece bucket side pos 1 - floors.piece bucket side pos 0) * time +
      floors.piece bucket side pos 0 = floors.piece bucket side pos time := by
  unfold piece base
  rw [← ep.carrier_affine floors.carrierScale pos.1 time]
  simp only [Phases.ramp, div_eq_mul_inv]
  split <;> ring

def value (bucket : Fin buckets) (side : Bool) (time : ℝ) :=
  peak (fun pos => floors.piece bucket side pos time)

theorem lower (bucket side time) : 1 ≤ floors.value bucket side time := by
  have hh := le_peak (fun pos => floors.piece bucket side pos time) (0, false)
  change floors.piece bucket side (0, false) time ≤ floors.value bucket side time at hh
  simpa [piece, base, Episodes.carrier] using hh

theorem upper : ∃ cap ≥ 1, ∀ bucket side time, time ∈ Icc (0 : ℝ) 1 → floors.value bucket side time ≤ cap := by
  have hh : ∀ pair : Fin buckets × Bool, ∃ val, ∀ time ∈ Icc (0 : ℝ) 1,
      floors.value pair.1 pair.2 time ≤ val := by
    intro pair
    have hc : Continuous (floors.value pair.1 pair.2) := by
      apply continuous_peak
      intro pos
      have he := funext (floors.affine pair.1 pair.2 pos)
      rw [← he]
      fun_prop
    obtain ⟨val, hv⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).image hc).bddAbove
    exact ⟨val, fun _ ht => hv (mem_image_of_mem _ ht)⟩
  choose val hv using hh
  obtain ⟨cap, hb⟩ := Finite.bddAbove_range val
  exact ⟨max 1 cap, le_max_left .., fun bucket side time ht =>
    ((hv (bucket, side) time ht).trans (hb (mem_range_self _))).trans (le_max_right ..)⟩

theorem on_episode (idx bucket side) {time : ℝ} (ht : time ∈ Icc (ep.left idx) (ep.right idx)) :
    floors.value bucket side time = floors.base idx time + max 0 ((phase idx bucket).ramp side time) := by
  let val := fun pos => floors.piece bucket side pos time
  apply le_antisymm
  · obtain ⟨⟨other, tag⟩, he⟩ := peak_attained val
    change peak val ≤ _
    rw [he]
    by_cases hn : idx = other
    · subst other
      cases tag <;> simp [val, piece]
    have hb := floors.bounded other bucket side time
      ⟨(ep.positive idx).le.trans ht.1, ht.2.trans (ep.interior idx).le⟩
    have hd := mul_le_mul_of_nonneg_left (ep.carrier_dominates floors.positive floors.gaps hn ht)
      floors.boundPos.le
    have hz := le_max_left 0 ((phase idx bucket).ramp side time)
    cases tag <;> simp only [val, piece, base, Bool.false_eq_true, ↓reduceIte] <;> linarith [floors.boundPos]
  · rw [add_max]
    exact max_le (le_peak val (idx, false)) (le_peak val (idx, true))

end Floors
end OAI.Geometry.Hirsch

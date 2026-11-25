import OAI.Geometry.Hirsch.Admissibility
import OAI.Geometry.Hirsch.Crossing

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

theorem hits_mark {len : ℕ} (time : Fin (len + 1) → ℝ) {mark : ℝ}
    (hspan : mark ∈ Ioo (min (time 0) (time (Fin.last len))) (max (time 0) (time (Fin.last len))))
    (hstep : ∀ idx : Fin len,
      mark ∉ Ioo (min (time idx.castSucc) (time idx.succ)) (max (time idx.castSucc) (time idx.succ))) :
    mark ∈ (Finset.Ioo 0 (Fin.last len)).image time := by
  have hex : ∃ idx, time idx = mark := by
    by_contra! hn
    have hh : ∀ idx, time idx < mark ↔ time 0 < mark := by
      intro idx
      induction idx using Fin.induction with
      | zero => rfl
      | succ idx ih =>
        rw [← ih]
        have hs := hstep idx
        have hf := hn idx.castSucc
        have hl := hn idx.succ
        grind
    specialize hh (Fin.last len)
    grind
  obtain ⟨idx, hi⟩ := hex
  refine Finset.mem_image.mpr ⟨idx, Finset.mem_Ioo.mpr ⟨?_, ?_⟩, hi⟩
  · apply lt_of_le_of_ne (Fin.zero_le idx)
    intro he
    rw [← he] at hi
    grind
  · apply lt_of_le_of_ne (Fin.le_last idx)
    intro he
    rw [he] at hi
    grind

namespace Tracer

variable (marks : Finset ℝ) (Coord : Type)

abbrev Piece := Option (marks × Bool)

def cut : Piece marks → Finset ℝ
  | none => ∅
  | some (mark, false) => marks.filter (· < mark.val)
  | some (mark, true) => marks.filter (· ≤ mark.val)

def floor (time : ℝ) : ℝ := ∑ mark ∈ marks, max 0 (time - mark)

def height (piece : Piece marks) (time : ℝ) : ℝ :=
  ∑ mark ∈ cut marks piece, (time - mark)

theorem height_le (piece : Piece marks) (time : ℝ) : height marks piece time ≤ floor marks time := by
  have hc : cut marks piece ⊆ marks := by
    rcases piece with _ | ⟨mark, _ | _⟩ <;> simp [cut]
  exact (Finset.sum_le_sum fun _ _ => le_max_right _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hc (fun _ _ _ => le_max_left _ _))

theorem height_left (mark : marks) : height marks (some (mark, false)) mark = floor marks mark := by
  unfold height floor cut
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro other _
  split <;> grind

theorem height_right (mark : marks) (time : ℝ) :
    height marks (some (mark, true)) time =
      time - mark + height marks (some (mark, false)) time := by
  have he : cut marks (some (mark, true)) = insert mark.val (cut marks (some (mark, false))) := by
    ext other
    simp only [cut, Finset.mem_filter, Finset.mem_insert]
    grind [mark.property]
  unfold height
  rw [he, Finset.sum_insert (by simp [cut])]

def block : Blocking Coord (Coord × Piece marks) where
  coeff row := LinearMap.proj row.1
  slope row := (cut marks row.2).card
  offset row := -∑ mark ∈ cut marks row.2, mark
  monotone row := fun _ _ hh => hh row.1
  positive _ := zero_lt_one
  individual idx := ⟨(idx, none), 1, one_pos, (one_smul _ _).symm⟩

variable {Coord}

theorem rhs (time : ℝ) (idx : Coord) (piece : Piece marks) :
    ((block marks Coord).slice time).rhs (idx, piece) = height marks piece time := by
  unfold height
  rw [Finset.sum_sub_distrib (fun _ => time) (fun mark : ℝ => mark)]
  simp [Blocking.slice, block, sub_eq_add_neg]

theorem active_iff (pt : Timed Coord) (idx : Coord) (piece : Piece marks) :
    (idx, piece) ∈ (block marks Coord).system.active pt ↔ pt.2 idx = height marks piece pt.1 := by
  rw [← Blocking.active_slice]
  change pt.2 idx = _ ↔ _
  rw [rhs]

theorem no_straddle [Finite Coord] {viable : Set Coord → Prop} {limit : ℕ}
    (hv : ∀ usable, viable usable → limit < usable.ncard) (mark : marks)
    {first last : Timed Coord}
    (hseg : segment ℝ first last ⊆ (block marks Coord).admissible viable limit) :
    mark.val ∉ Ioo (min first.1 last.1) (max first.1 last.1) := by
  intro hm
  have hn : first.1 ≠ last.1 := by grind
  let proj := (LinearMap.fst ℝ ℝ (Vec Coord)).toAffineMap
  have hh : mark.val ∈ proj '' openSegment ℝ first last := by
    rw [image_openSegment]
    exact (openSegment_eq_Ioo' hn).symm ▸ hm
  obtain ⟨pt, hp, he⟩ := hh
  change pt.1 = mark.val at he
  have hf := hseg (left_mem_segment ℝ first last)
  have hl := hseg (right_mem_segment ℝ first last)
  have ha := hseg (openSegment_subset_segment _ _ _ hp)
  obtain ⟨⟨idx, piece⟩, hr⟩ := (block marks Coord).exists_tight hv ha
  have hle := ((block marks Coord).mem_slice pt).mpr ha.1 (idx, some (mark, false))
  rw [rhs, he, height_left] at hle
  have heq : pt.2 idx = floor marks mark := le_antisymm
    (((active_iff marks pt idx piece).mp hr).trans_le (he ▸ height_le marks piece mark.val)) hle
  have ht : ∀ side : Bool, first.2 idx = height marks (some (mark, side)) first.1 := by
    intro side
    apply (active_iff marks first idx _).mp
    have hmid : (idx, some (mark, side)) ∈ (block marks Coord).system.active pt := by
      rw [active_iff, he, heq]
      cases side <;> simp [height_right, height_left]
    rw [System.active_openSegment hf.1 hl.1 hp] at hmid
    exact hmid.1
  have eqn := height_right marks mark first.1
  rw [← ht true, ← ht false] at eqn
  have he' : first.1 = mark.val := by linarith
  grind

theorem crossing [Finite Coord] {viable : Set Coord → Prop} {limit : ℕ}
    (hv : ∀ usable, viable usable → limit < usable.ncard) {left right : ℝ} (hw : left < right) :
    CrossingBound ((block marks Coord).admissible viable limit) left right
      ((marks.filter (· ∈ Ioo left right)).card + 1) := by
  intro len pts hseg hspan
  let time := fun idx => (pts idx).1
  have hpos : 0 < len := by
    by_contra! hn
    have he : Fin.last len = 0 := Fin.ext (by simpa using Nat.eq_zero_of_le_zero hn)
    simp [Spans, he] at hspan
    linarith
  have hsub : marks.filter (· ∈ Ioo left right) ⊆ (Finset.Ioo 0 (Fin.last len)).image time := by
    intro mark hm
    obtain ⟨hm, hl, hr⟩ := Finset.mem_filter.mp hm
    exact hits_mark time ⟨hspan.1.trans_lt hl, hr.trans_le hspan.2⟩
      (fun idx => no_straddle marks hv ⟨mark, hm⟩ (hseg idx))
  have hc := (Finset.card_le_card hsub).trans Finset.card_image_le
  simp only [Fin.card_Ioo, Fin.val_last, Fin.val_zero, Nat.sub_zero] at hc
  omega

end Tracer
end OAI.Geometry.Hirsch

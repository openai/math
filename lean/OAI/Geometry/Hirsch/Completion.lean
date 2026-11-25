import OAI.Geometry.Hirsch.Regular

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.System

variable {Space Row : Type} [AddCommGroup Space] [Module ℝ Space] [Finite Row]
  {sys : System Space Row} {pt dir : Space}

theorem first_contact (hp : pt ∈ sys.body) (hn : ∃ row, sys.normal row dir < 0) :
    ∃ scale : ℝ, 0 ≤ scale ∧ pt + scale • dir ∈ sys.body ∧
      ∃ row ∈ sys.active (pt + scale • dir), sys.normal row dir < 0 := by
  let falling := {row | sys.normal row dir < 0}
  let ratio := fun row => (sys.normal row pt - sys.rhs row) / (-sys.normal row dir)
  obtain ⟨pivot, hf, hmin⟩ := exists_min_image falling ratio (toFinite _) hn
  have hh : 0 < -sys.normal pivot dir := neg_pos.mpr hf
  have hr : 0 ≤ ratio pivot := div_nonneg (sub_nonneg.mpr (hp pivot)) hh.le
  refine ⟨ratio pivot, hr, ?_, pivot, ?_, hf⟩
  · intro row
    rw [map_add, map_smul, smul_eq_mul]
    by_cases hl : sys.normal row dir < 0
    · have he := (le_div_iff₀ (neg_pos.mpr hl)).mp (hmin row hl)
      linarith
    · linarith [hp row, mul_nonneg hr (le_of_not_gt hl)]
  · change sys.normal pivot _ = _
    rw [map_add, map_smul, smul_eq_mul]
    have he : ratio pivot * (-sys.normal pivot dir) = _ := div_mul_cancel₀ _ hh.ne'
    linarith

theorem deletion (used : Set Row) (hu : sys.used ⊆ used) (hne : sys.body.Nonempty)
    (hp : ∀ row ∈ used, sys.rhs row ≤ sys.normal row pt) : pt ∈ sys.body := by
  by_contra hn
  simp only [body, mem_ofPred_eq, not_forall, not_le] at hn
  obtain ⟨bad, hb⟩ := hn
  obtain ⟨base, hf⟩ := hne
  have hh : sys.normal bad (pt - base) < 0 := by rw [map_sub]; linarith [hf bad]
  obtain ⟨scale, _, hm, pivot, ht, hl⟩ := first_contact hf ⟨bad, hh⟩
  have hs : scale < 1 := by
    have he := hm bad
    rw [map_add, map_smul, smul_eq_mul, map_sub] at he
    nlinarith [hf bad]
  have he := hp pivot (hu ⟨_, hm, ht⟩)
  change sys.normal pivot _ = _ at ht
  rw [map_add, map_smul, smul_eq_mul] at ht
  have hlt := mul_lt_mul_of_neg_right hs hl
  rw [map_sub] at ht hlt
  linarith

theorem complete_vertex (pointed : sys.directions univ = ⊥) (hp : pt ∈ sys.body) :
    ∃ best ∈ sys.body.extremePoints ℝ, sys.active pt ⊆ sys.active best := by
  let candidates := sys.active '' sys.locus (sys.active pt)
  have hne : candidates.Nonempty := ⟨_, pt, ⟨hp, Subset.rfl⟩, rfl⟩
  obtain ⟨_, ⟨best, hb, rfl⟩, hmax⟩ := exists_max_image candidates Set.ncard (toFinite _) hne
  refine ⟨best, (vertex_iff hb.1).mpr ?_, hb.2⟩
  by_contra hn
  obtain ⟨dir, hd, hd'⟩ := (Submodule.ne_bot_iff _).mp hn
  have hex : ∃ row, sys.normal row dir ≠ 0 := by
    by_contra! hh
    have hz := sys.mem_directions.mpr (show ∀ row ∈ univ, sys.normal row dir = 0 from fun row _ => hh row)
    rw [pointed] at hz
    exact hd' hz
  obtain ⟨row, hr⟩ := hex
  have hf : ∃ shift ∈ sys.directions (sys.active best), sys.normal row shift < 0 := by
    rcases lt_or_gt_of_ne hr with hh | hh
    · exact ⟨dir, hd, hh⟩
    · exact ⟨-dir, Submodule.neg_mem _ hd, by simpa using hh⟩
  obtain ⟨shift, hshift, hf⟩ := hf
  obtain ⟨scale, _, hm, pivot, ht, hl⟩ := first_contact hb.1 ⟨row, hf⟩
  have hs : sys.active best ⊆ sys.active (best + scale • shift) := by
    intro idx hi
    change sys.normal idx _ = _
    rw [map_add, map_smul, sys.mem_directions.mp hshift idx hi, smul_zero, add_zero]
    exact hi
  have hlt : sys.active best ⊂ sys.active (best + scale • shift) :=
    ssubset_iff_subset_ne.mpr ⟨hs, fun he => hl.ne (sys.mem_directions.mp hshift pivot (he.symm ▸ ht))⟩
  exact (ncard_lt_ncard hlt).not_ge (hmax _ ⟨_, ⟨hm, hb.2.trans hs⟩, rfl⟩)

end OAI.Geometry.Hirsch.System

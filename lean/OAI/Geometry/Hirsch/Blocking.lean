import OAI.Geometry.Hirsch.Stability

noncomputable section

open Set Module

namespace OAI.Geometry.Hirsch

abbrev Vec (Coord : Type) := Coord → ℝ
abbrev Timed (Coord : Type) := ℝ × Vec Coord

structure Blocking (Coord Row : Type) where
  coeff : Row → Vec Coord →ₗ[ℝ] ℝ
  slope : Row → ℝ
  offset : Row → ℝ
  monotone : ∀ row, Monotone (coeff row)
  positive : ∀ row, 0 < coeff row 1
  individual : ∀ coord, ∃ row, ∃ weight : ℝ, 0 < weight ∧
    coeff row = weight • LinearMap.proj coord

namespace Blocking

variable {Coord Row : Type} (block : Blocking Coord Row)

def slice (time : ℝ) : System (Vec Coord) Row :=
  ⟨block.coeff, fun row => block.slope row * time + block.offset row⟩

def system : System (Timed Coord) Row :=
  ⟨fun row => (block.coeff row).comp (LinearMap.snd ℝ _ _) -
    block.slope row • LinearMap.fst ℝ _ _, block.offset⟩

theorem mem_slice (pt : Timed Coord) :
    pt.2 ∈ (block.slice pt.1).body ↔ pt ∈ block.system.body := by
  simp [slice, system, System.body, le_sub_iff_add_le, add_comm]

theorem active_slice (pt : Timed Coord) :
    (block.slice pt.1).active pt.2 = block.system.active pt := by
  ext row
  simp [slice, system, System.active, sub_eq_iff_eq_add, add_comm]

def thin (limit : ℕ) : Set (Timed Coord) :=
  {pt ∈ block.system.body | finrank ℝ ((block.slice pt.1).directions (block.system.active pt)) ≤ limit}

theorem thin_iff [Finite Row] [Finite Coord] (limit : ℕ) (pt : Timed Coord) :
    pt ∈ block.thin limit ↔ ∃ face, IsFace (block.slice pt.1).body face ∧
      pt.2 ∈ face ∧ dim face ≤ limit := by
  let sys := block.slice pt.1
  change pt ∈ block.system.body ∧ finrank ℝ (sys.directions (block.system.active pt)) ≤ limit ↔ _
  rw [← mem_slice, ← active_slice]
  constructor
  · rintro ⟨hp, hd⟩
    exact ⟨sys.locus (sys.active pt.2), sys.isFace_locus _, ⟨hp, Subset.rfl⟩,
      by rw [dim, System.vectorSpan_active hp]; exact hd⟩
  · rintro ⟨face, hf, hp, hd⟩
    have hm := hf.extreme.subset hp
    refine ⟨hm, ?_⟩
    rw [← System.vectorSpan_active hm]
    exact (Submodule.finrank_mono (vectorSpan_mono ℝ (System.locus_minimal hf.extreme hp))).trans hd

variable [Fintype Coord] [Fintype Row]

def total : Vec Coord →ₗ[ℝ] ℝ := ∑ idx, LinearMap.proj idx

@[simp] theorem total_apply (vec : Vec Coord) : total vec = ∑ idx, vec idx := by
  simp [total, LinearMap.sum_apply]

def capped (margin roof : ℝ) : System (Timed Coord) (Row ⊕ Option Bool) where
  normal
    | .inl row => block.system.normal row
    | .inr none => -total.comp (LinearMap.snd ℝ _ _)
    | .inr (some false) => LinearMap.fst ℝ _ _
    | .inr (some true) => -LinearMap.fst ℝ _ _
  rhs
    | .inl row => block.system.rhs row
    | .inr none => -roof
    | .inr (some false) => -margin
    | .inr (some true) => -(1 + margin)

omit [Fintype Row] in
theorem mem_capped {margin roof : ℝ} {pt : Timed Coord} :
    pt ∈ (block.capped margin roof).body ↔ pt ∈ block.system.body ∧
      pt.1 ∈ Icc (-margin) (1 + margin) ∧ total pt.2 ≤ roof := by
  constructor
  · intro hp
    exact ⟨fun row => hp (.inl row), ⟨hp (.inr (some false)), neg_le_neg_iff.mp (hp (.inr (some true)))⟩,
      neg_le_neg_iff.mp (hp (.inr none))⟩
  · rintro ⟨hp, ⟨hl, hu⟩, ht⟩ (row | (_ | (_ | _)))
    exacts [hp row, neg_le_neg ht, hl, neg_le_neg hu]

theorem strict_witnesses {margin : ℝ} (hm : 0 < margin) :
    ∃ roof vec, ∀ time ∈ Icc (0 : ℝ) 1,
      (Data.ofSystem (block.capped margin roof)).Strict (time, vec) := by
  obtain ⟨level, hl⟩ := Finite.bddAbove_range
    (fun row => (|block.slope row| + block.offset row) / block.coeff row 1)
  let vec : Vec Coord := (level + 1) • 1
  refine ⟨total vec + 1, vec, ?_⟩
  rintro time ⟨ht, hu⟩ (row | (_ | (_ | _)))
  · change block.offset row < block.coeff row vec - block.slope row * time
    have hc := (div_le_iff₀ (block.positive row)).mp (hl (mem_range_self row))
    have hs := (mul_le_mul_of_nonneg_right (le_abs_self (block.slope row)) ht).trans
      (mul_le_of_le_one_right (abs_nonneg _) hu)
    rw [show vec = _ from rfl, map_smul, smul_eq_mul]
    linarith [block.positive row]
  · change -(total vec + 1) < -total vec
    linarith
  · change -margin < time
    linarith
  · change -(1 + margin) < -time
    linarith

omit [Fintype Row] in
theorem compact_capped (margin roof : ℝ) : IsCompact (block.capped margin roof).body := by
  classical
  choose row weight hw he using block.individual
  let lower := fun idx => (block.offset (row idx) - |block.slope (row idx)| * (1 + margin)) / weight idx
  let upper := fun idx => roof - ∑ other ∈ Finset.univ.erase idx, lower other
  apply (isCompact_Icc (a := (-margin, lower)) (b := (1 + margin, upper))).of_isClosed_subset
    (block.capped margin roof).isClosed_body
  intro pt hp
  obtain ⟨hf, ht, hu⟩ := block.mem_capped.mp hp
  have hl : lower ≤ pt.2 := by
    intro idx
    apply (div_le_iff₀ (hw idx)).mpr
    have hh := (block.mem_slice pt).mpr hf (row idx)
    change block.slope (row idx) * pt.1 + block.offset (row idx) ≤ block.coeff (row idx) pt.2 at hh
    rw [he idx, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul] at hh
    have hab : |pt.1| ≤ 1 + margin := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have hv := mul_le_mul_of_nonneg_left hab (abs_nonneg (block.slope (row idx)))
    rw [← abs_mul] at hv
    linarith [neg_abs_le (block.slope (row idx) * pt.1)]
  refine ⟨⟨ht.1, hl⟩, ht.2, fun idx => ?_⟩
  have hh := Finset.sum_le_sum (s := Finset.univ.erase idx) (fun other _ => hl other)
  rw [total_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ idx)] at hu
  change pt.2 idx ≤ roof - _
  linarith

omit [Fintype Row] in
theorem thin_of_capped {margin roof : ℝ} {moves : ℕ} {rows : Set (Row ⊕ Option Bool)}
    {pt : Timed Coord} (hp : pt ∈ (block.capped margin roof).locus rows)
    (hd : (block.capped margin roof).lowDim moves rows) :
    pt ∈ block.thin (moves + 1) := by
  let dirs := (block.slice pt.1).directions (block.system.active pt)
  let sumDir := total.domRestrict dirs
  let embed := (LinearMap.inr ℝ ℝ (Vec Coord)).comp dirs.subtype
  have hmap : ∀ dir ∈ sumDir.ker, embed dir ∈ (block.capped margin roof).directions rows := by
    intro dir hz
    apply (System.mem_directions _).mpr
    rintro (row | (_ | (_ | _))) hr
    · have ha : row ∈ block.system.active pt := hp.2 hr
      have hh := ((block.slice pt.1).mem_directions.mp dir.property) row ha
      change block.coeff row dir.val - block.slope row * 0 = 0
      simpa [slice] using hh
    · change -total dir.val = 0
      exact neg_eq_zero.mpr hz
    · rfl
    · exact neg_zero
  have hi : Function.Injective (embed.restrict hmap) := by
    intro first last he
    exact Subtype.ext (Subtype.ext (congrArg (fun v => v.val.2) he))
  have hk := (LinearMap.finrank_le_finrank_of_injective hi).trans hd
  have hr : finrank ℝ sumDir.range ≤ 1 := by simpa using sumDir.range.finrank_le
  have he := sumDir.finrank_range_add_finrank_ker
  refine ⟨(block.mem_capped.mp hp.1).1, ?_⟩
  change finrank ℝ dirs ≤ moves + 1
  omega

end Blocking
end OAI.Geometry.Hirsch

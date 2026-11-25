import OAI.Geometry.Hirsch.Blocking

noncomputable section

open Set Module

namespace OAI.Geometry.Hirsch

variable {Coord Row : Type}

def supported (usable : Set Coord) : Submodule ℝ (Vec Coord) where
  carrier := {vec | ∀ idx ∉ usable, vec idx = 0}
  zero_mem' := by simp
  add_mem' := fun hf hl idx hi => by simp [hf idx hi, hl idx hi]
  smul_mem' := fun _ _ hv idx hi => by simp [hv idx hi]

def supportedEquiv (usable : Set Coord) : supported usable ≃ₗ[ℝ] (usable → ℝ) := by
  classical
  exact {
    toFun := fun vec idx => vec.val idx.val
    invFun := fun vec => ⟨fun idx => if hi : idx ∈ usable then vec ⟨idx, hi⟩ else 0,
      fun idx hi => by simp [hi]⟩
    left_inv := by
      intro vec
      ext idx
      by_cases hi : idx ∈ usable
      · simp [hi]
      · simp [hi, vec.property idx hi]
    right_inv := by intro vec; ext idx; simp
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

theorem finrank_supported [Finite Coord] (usable : Set Coord) :
    finrank ℝ (supported usable) = usable.ncard := by
  let := Fintype.ofFinite usable
  rw [(supportedEquiv usable).finrank_eq, finrank_pi, fintypeCard_eq_ncard]

namespace Blocking

variable (block : Blocking Coord Row)

def support (row : Row) : Set Coord := by
  classical
  exact {idx | block.coeff row (Pi.single idx 1) ≠ 0}

def nullspace (tight : Set Row) (usable : Set Coord) : Submodule ℝ (Vec Coord) :=
  supported usable ⊓ (block.slice 0).directions tight

def certified (viable : Set Coord → Prop) (limit : ℕ) (tight : Set Row) : Prop :=
  ∃ usable, viable usable ∧ (∀ row ∈ tight, block.support row ⊆ usable) ∧
    finrank ℝ (block.nullspace tight usable) ≤ limit

def admissible (viable : Set Coord → Prop) (limit : ℕ) : Set (Timed Coord) :=
  {pt ∈ block.system.body | block.certified viable limit (block.system.active pt)}

variable {viable : Set Coord → Prop} {limit : ℕ}

theorem thin_admissible [Finite Coord] (hv : viable univ) :
    block.thin limit ⊆ block.admissible viable limit := by
  rintro pt ⟨hp, hd⟩
  exact ⟨hp, univ, hv, fun _ _ => subset_univ _, (Submodule.finrank_mono inf_le_right).trans hd⟩

theorem exists_tight [Finite Coord] (hv : ∀ usable, viable usable → limit < usable.ncard)
    {pt : Timed Coord} (hp : pt ∈ block.admissible viable limit) :
    (block.system.active pt).Nonempty := by
  obtain ⟨_, usable, hu, _, hd⟩ := hp
  by_contra hn
  have he : block.nullspace (block.system.active pt) usable = supported usable := by
    simp [nullspace, System.directions, not_nonempty_iff_eq_empty.mp hn]
  rw [he, finrank_supported] at hd
  exact (hv usable hu).not_ge hd

theorem chord {first last : Timed Coord} (hf : first ∈ block.admissible viable limit)
    (hl : last ∈ block.admissible viable limit)
    (ha : block.system.active first ⊆ block.system.active last) :
    segment ℝ first last ⊆ block.admissible viable limit := by
  rw [← insert_endpoints_openSegment, insert_subset_iff, insert_subset_iff]
  refine ⟨hf, hl, fun pt hp => ⟨block.system.convex_body.segment_subset hf.1 hl.1
    (openSegment_subset_segment _ _ _ hp), ?_⟩⟩
  rw [System.active_openSegment hf.1 hl.1 hp, inter_eq_left.mpr ha]
  exact hf.2

theorem two_chords {first mid last : Timed Coord} (hf : first ∈ block.admissible viable limit)
    (hm : mid ∈ block.admissible viable limit) (hl : last ∈ block.admissible viable limit)
    (ht : mid.1 = (first.1 + last.1) / 2)
    (hz : (1 / 2 : ℝ) • (first.2 + last.2) ≤ mid.2) :
    segment ℝ first mid ⊆ block.admissible viable limit ∧
      segment ℝ mid last ⊆ block.admissible viable limit := by
  let avg := (1 / 2 : ℝ) • first + (1 / 2 : ℝ) • last
  have ha : avg ∈ openSegment ℝ first last := ⟨_, _, by norm_num, by norm_num, by norm_num, rfl⟩
  have hb := block.system.convex_body.segment_subset hf.1 hl.1 (openSegment_subset_segment _ _ _ ha)
  have hs : block.system.active mid ⊆ block.system.active avg := by
    intro row hr
    apply le_antisymm _ (hb row)
    rw [← show block.system.normal row mid = _ from hr]
    change block.coeff row avg.2 - block.slope row * avg.1 ≤
      block.coeff row mid.2 - block.slope row * mid.1
    have he : avg.1 = mid.1 := by rw [ht]; dsimp [avg]; ring
    rw [he]
    exact sub_le_sub_right (block.monotone row (by simpa [avg, smul_add] using hz)) _
  rw [System.active_openSegment hf.1 hl.1 ha] at hs
  rw [segment_symm ℝ first mid]
  exact ⟨block.chord hm hf (hs.trans inter_subset_left), block.chord hm hl (hs.trans inter_subset_right)⟩

end Blocking
end OAI.Geometry.Hirsch

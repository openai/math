import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

noncomputable section

open Set Filter Module
open scoped Topology

namespace OAI.Geometry.Hirsch

variable {Space : Type} [AddCommGroup Space] [Module ℝ Space]

structure IsFace (body face : Set Space) : Prop where
  convex : Convex ℝ face
  extreme : IsExtreme ℝ body face

def dim (face : Set Space) : ℕ := finrank ℝ (vectorSpan ℝ face)

def facets (body : Set Space) : Set (Set Space) :=
  {face | IsFace body face ∧ face.Nonempty ∧ dim face + 1 = dim body}

def Simple (body : Set Space) : Prop :=
  ∀ point ∈ body.extremePoints ℝ, {face ∈ facets body | point ∈ face}.ncard = dim body

structure System (Space : Type) [AddCommGroup Space] [Module ℝ Space] (Row : Type) where
  normal : Row → Space →ₗ[ℝ] ℝ
  rhs : Row → ℝ

namespace System

variable {Row : Type} (sys : System Space Row)

def body : Set Space := {point | ∀ row, sys.rhs row ≤ sys.normal row point}

def active (point : Space) : Set Row :=
  {row | sys.normal row point = sys.rhs row}

def locus (rows : Set Row) : Set Space :=
  {point ∈ sys.body | rows ⊆ sys.active point}

def directions (rows : Set Row) : Submodule ℝ Space :=
  ⨅ row ∈ rows, (sys.normal row).ker

theorem mem_directions {rows : Set Row} {dir : Space} :
    dir ∈ sys.directions rows ↔ ∀ row ∈ rows, sys.normal row dir = 0 := by
  simp [directions, LinearMap.mem_ker]

variable {sys} {first last point dir : Space} {rows : Set Row}

theorem sub_mem_directions (hf : rows ⊆ sys.active first) (hl : rows ⊆ sys.active last) :
    first - last ∈ sys.directions rows := by
  refine sys.mem_directions.mpr fun row hr => ?_
  rw [map_sub, show sys.normal row first = _ from hf hr,
    show sys.normal row last = _ from hl hr, sub_self]

theorem vectorSpan_locus_le :
    vectorSpan ℝ (sys.locus rows) ≤ sys.directions rows := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro _ ⟨first, hf, last, hl, rfl⟩
  exact sub_mem_directions hf.2 hl.2

theorem convex_body (sys : System Space Row) : Convex ℝ sys.body := by
  intro first hf last hl left right hleft hright hsum row
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  calc
    _ = left * sys.rhs row + right * sys.rhs row := by rw [← add_mul, hsum, one_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hf row) hleft)
      (mul_le_mul_of_nonneg_left (hl row) hright)

theorem active_openSegment (hf : first ∈ sys.body) (hl : last ∈ sys.body)
    (hp : point ∈ openSegment ℝ first last) :
    sys.active point = sys.active first ∩ sys.active last := by
  obtain ⟨left, right, hleft, hright, hsum, rfl⟩ := hp
  ext row
  simp only [active, mem_ofPred_eq, mem_inter_iff, map_add, map_smul, smul_eq_mul]
  have eqn : left * sys.rhs row + right * sys.rhs row = sys.rhs row := by
    rw [← add_mul, hsum, one_mul]
  constructor
  · intro heq
    constructor
    · apply le_antisymm _ (hf row)
      apply le_of_mul_le_mul_left _ hleft
      linarith [mul_le_mul_of_nonneg_left (hl row) hright.le]
    · apply le_antisymm _ (hl row)
      apply le_of_mul_le_mul_left _ hright
      linarith [mul_le_mul_of_nonneg_left (hf row) hleft.le]
  · rintro ⟨he, he'⟩
    rw [he, he', eqn]

theorem isFace_locus (sys : System Space Row) (rows : Set Row) :
    IsFace sys.body (sys.locus rows) := by
  constructor
  · intro first hf last hl left right hleft hright hsum
    refine ⟨sys.convex_body hf.1 hl.1 hleft hright hsum, fun row hr => ?_⟩
    change sys.normal row _ = _
    rw [map_add, map_smul, map_smul, show sys.normal row first = _ from hf.2 hr,
      show sys.normal row last = _ from hl.2 hr, ← add_smul, hsum, one_smul]
  · refine ⟨fun _ hp => hp.1, fun _ hf _ hl _ hp hseg => ⟨hf, ?_⟩⟩
    exact hp.2.trans ((active_openSegment hf hl hseg).subset.trans inter_subset_left)

variable [Finite Row]

theorem step (hp : point ∈ sys.body)
    (hd : ∀ row ∈ sys.active point, 0 ≤ sys.normal row dir) :
    ∃ scale : ℝ, 0 < scale ∧ point + scale • dir ∈ sys.body ∧
      sys.active (point + scale • dir) =
        {row ∈ sys.active point | sys.normal row dir = 0} := by
  have hev : ∀ᶠ scale : ℝ in 𝓝 0, ∀ row ∉ sys.active point,
      sys.rhs row < sys.normal row (point + scale • dir) := by
    apply eventually_all.mpr
    intro row
    by_cases hr : row ∈ sys.active point
    · exact Eventually.of_forall fun _ hn => (hn hr).elim
    have hlt : sys.rhs row < sys.normal row point := lt_of_le_of_ne (hp row) (Ne.symm hr)
    have hc : Continuous (fun scale : ℝ => sys.normal row point + scale * sys.normal row dir) :=
      continuous_const.add (continuous_id.mul continuous_const)
    have hh := hc.continuousAt (x := (0 : ℝ))
    filter_upwards [hh.eventually (eventually_gt_nhds (by simpa using hlt))] with scale hs _
    simpa using hs
  obtain ⟨scale, hs, he⟩ := (eventually_mem_nhdsWithin.and
    (hev.filter_mono nhdsWithin_le_nhds) : ∀ᶠ scale in 𝓝[>] (0 : ℝ), scale ∈ Ioi 0 ∧ _).exists
  change 0 < scale at hs
  refine ⟨scale, hs, ?_, ?_⟩
  · intro row
    by_cases hr : row ∈ sys.active point
    · rw [map_add, map_smul, smul_eq_mul, show sys.normal row point = _ from hr]
      exact le_add_of_nonneg_right (mul_nonneg hs.le (hd row hr))
    · exact (he row hr).le
  · ext row
    by_cases hr : row ∈ sys.active point
    · change sys.normal row point = sys.rhs row at hr
      simp [active, hr, hs.ne']
    · exact iff_of_false (he row hr).ne' (fun hh => hr hh.1)

theorem step_directions (hp : point ∈ sys.body) (hd : dir ∈ sys.directions (sys.active point)) :
    ∃ scale : ℝ, 0 < scale ∧ point + scale • dir ∈ sys.locus (sys.active point) := by
  have hz := sys.mem_directions.mp hd
  obtain ⟨scale, hs, hf, he⟩ := step hp (fun row hr => (hz row hr).ge)
  exact ⟨scale, hs, hf, he.symm ▸ fun row hr => ⟨hr, hz row hr⟩⟩

theorem vectorSpan_active (hp : point ∈ sys.body) :
    vectorSpan ℝ (sys.locus (sys.active point)) = sys.directions (sys.active point) := by
  apply le_antisymm vectorSpan_locus_le
  intro dir hd
  obtain ⟨scale, hs, hf⟩ := step_directions hp hd
  have hh := vsub_mem_vectorSpan ℝ hf (show point ∈ sys.locus (sys.active point) from ⟨hp, Subset.rfl⟩)
  rw [vsub_eq_sub, add_sub_cancel_left] at hh
  simpa [smul_smul, hs.ne'] using (vectorSpan ℝ _).smul_mem scale⁻¹ hh

theorem locus_minimal {face : Set Space} (he : IsExtreme ℝ sys.body face) (hp : point ∈ face) :
    sys.locus (sys.active point) ⊆ face := by
  intro first hf
  obtain ⟨scale, hs, hl⟩ := step_directions (he.subset hp)
    (sub_mem_directions (first := point) Subset.rfl hf.2)
  apply he.left_mem_of_mem_openSegment hf.1 hl.1 hp
  have hpos : 0 < 1 + scale := by linarith
  refine ⟨scale / (1 + scale), 1 / (1 + scale), div_pos hs hpos,
    div_pos one_pos hpos, by rw [← add_div, add_comm scale, div_self hpos.ne'], ?_⟩
  match_scalars <;> field_simp
  ring

theorem face_eq_locus {face : Set Space} (hf : IsFace sys.body face) (hne : face.Nonempty) :
    ∃ point ∈ face, face = sys.locus (sys.active point) := by
  obtain ⟨point, hp, hmin⟩ := (measure fun point => (sys.active point).ncard).wf.has_min face hne
  refine ⟨point, hp, Subset.antisymm ?_ (locus_minimal hf.extreme hp)⟩
  intro last hl
  let : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  have hm := hf.convex.midpoint_mem hp hl
  have he := active_openSegment (hf.extreme.subset hp) (hf.extreme.subset hl)
    (midpoint_mem_openSegment point last (𝕜 := ℝ))
  have hc : (sys.active point).ncard ≤ (sys.active (midpoint ℝ point last)).ncard :=
    Nat.le_of_not_gt (hmin _ hm)
  rw [he] at hc
  have eqn := Set.eq_of_subset_of_ncard_le inter_subset_left hc
  exact ⟨hf.extreme.subset hl, eqn.symm.subset.trans inter_subset_right⟩

theorem vertex_iff (hp : point ∈ sys.body) :
    point ∈ sys.body.extremePoints ℝ ↔ sys.directions (sys.active point) = ⊥ := by
  rw [← vectorSpan_active hp, vectorSpan_eq_bot_iff_subsingleton]
  constructor
  · intro hv
    have he : IsExtreme ℝ sys.body {point} :=
      ⟨singleton_subset_iff.mpr hp, by rintro _ hf _ hl _ rfl hs; exact hv.2 hf hl hs⟩
    exact subsingleton_singleton.anti (locus_minimal he (mem_singleton point))
  · intro hh
    refine ⟨hp, fun _ hf _ hl hs => hh ?_ ⟨hp, Subset.rfl⟩⟩
    exact ⟨hf, (active_openSegment hf hl hs).subset.trans inter_subset_left⟩

end System
end OAI.Geometry.Hirsch

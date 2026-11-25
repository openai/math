import OAI.Geometry.Hirsch.Faces

noncomputable section

open Set Module

namespace OAI.Geometry.Hirsch.System

variable {Space Row : Type} [AddCommGroup Space] [Module ℝ Space]
variable (sys : System Space Row)

def evaluation (rows : Set Row) : Space →ₗ[ℝ] (rows → ℝ) :=
  LinearMap.pi fun row => sys.normal row

theorem ker_evaluation (rows : Set Row) :
    (sys.evaluation rows).ker = sys.directions rows := by
  ext dir
  simp [evaluation, mem_directions, funext_iff]

def Regular : Prop :=
  ∀ point ∈ sys.body, ∀ values : Row → ℝ,
    ∃ dir, ∀ row ∈ sys.active point, sys.normal row dir = values row

def used : Set Row := {row | ∃ point ∈ sys.body, row ∈ sys.active point}

def wall (row : Row) : Set Space := sys.locus {row}

variable {sys} {point : Space} {rows : Set Row}

theorem Regular.surjective (reg : sys.Regular) (hp : point ∈ sys.body)
    (hr : rows ⊆ sys.active point) : Function.Surjective (sys.evaluation rows) := by
  classical
  intro values
  obtain ⟨dir, hd⟩ := reg point hp fun row => if hh : row ∈ rows then values ⟨row, hh⟩ else 0
  refine ⟨dir, funext fun row => ?_⟩
  simpa [evaluation] using hd row (hr row.property)

variable [Finite Row]

theorem finite_vertices (sys : System Space Row) : (sys.body.extremePoints ℝ).Finite := by
  apply (Set.toFinite (sys.active '' sys.body.extremePoints ℝ)).of_finite_image
  intro first hf last hl he
  have hd := sub_mem_directions (sys := sys) (first := first) Subset.rfl he.subset
  rw [(vertex_iff hf.1).mp hf] at hd
  exact sub_eq_zero.mp hd

theorem finite_facets (sys : System Space Row) : (facets sys.body).Finite := by
  apply (Set.finite_range sys.locus).subset
  intro face hf
  obtain ⟨point, _, he⟩ := face_eq_locus hf.1 hf.2.1
  exact ⟨_, he.symm⟩

theorem Regular.realize (reg : sys.Regular) (hp : point ∈ sys.body)
    (hr : rows ⊆ sys.active point) :
    ∃ other ∈ sys.body, sys.active other = rows := by
  classical
  obtain ⟨dir, hd⟩ := reg point hp fun row => if row ∈ rows then 0 else 1
  have hn : ∀ row ∈ sys.active point, 0 ≤ sys.normal row dir := by
    intro row hh
    rw [hd row hh]
    split <;> norm_num
  obtain ⟨scale, _, hf, he⟩ := step hp hn
  refine ⟨_, hf, he.trans ?_⟩
  ext row
  by_cases hh : row ∈ sys.active point
  · simp [hh, hd row hh]
  · simp [hh, mt (fun hm => hr hm) hh]

theorem Regular.injOn_wall (reg : sys.Regular) : InjOn sys.wall sys.used := by
  intro first hf last _ he
  obtain ⟨point, hp, hh⟩ := hf
  obtain ⟨other, ho, heq⟩ := reg.realize hp (singleton_subset_iff.mpr hh)
  have hm : other ∈ sys.wall last := he ▸ (show other ∈ sys.wall first from ⟨ho, heq.symm.subset⟩)
  exact (mem_singleton_iff.mp (heq ▸ hm.2 (mem_singleton last))).symm

variable [FiniteDimensional ℝ Space]

theorem Regular.rank (reg : sys.Regular) (hp : point ∈ sys.body)
    (hr : rows ⊆ sys.active point) :
    rows.ncard + finrank ℝ (sys.directions rows) = finrank ℝ Space := by
  classical
  let := Fintype.ofFinite rows
  have he := (sys.evaluation rows).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (reg.surjective hp hr), finrank_top, finrank_pi,
    fintypeCard_eq_ncard, ker_evaluation] at he
  exact he

theorem Regular.dim_locus (reg : sys.Regular) (hp : point ∈ sys.body)
    (hr : rows ⊆ sys.active point) :
    rows.ncard + dim (sys.locus rows) = finrank ℝ Space := by
  obtain ⟨other, ho, rfl⟩ := reg.realize hp hr
  rw [dim, vectorSpan_active ho]
  exact reg.rank ho Subset.rfl

theorem Regular.dim_body (reg : sys.Regular) (hne : sys.body.Nonempty) :
    dim sys.body = finrank ℝ Space := by
  obtain ⟨point, hp⟩ := hne
  simpa [locus] using reg.dim_locus hp (empty_subset _)

theorem Regular.vertex_card (reg : sys.Regular) (hp : point ∈ sys.body) :
    point ∈ sys.body.extremePoints ℝ ↔ (sys.active point).ncard = finrank ℝ Space := by
  have he := reg.rank hp Subset.rfl
  rw [vertex_iff hp, ← Submodule.finrank_eq_zero]
  omega

theorem Regular.facets_eq (reg : sys.Regular) :
    facets sys.body = sys.wall '' sys.used := by
  ext face
  constructor
  · rintro ⟨hf, hne, hd⟩
    obtain ⟨point, hp, he⟩ := face_eq_locus hf hne
    have hb := hf.extreme.subset hp
    have hc := reg.dim_locus hb Subset.rfl
    rw [reg.dim_body ⟨point, hb⟩, he] at hd
    obtain ⟨row, hr⟩ := ncard_eq_one.mp (show (sys.active point).ncard = 1 by omega)
    exact ⟨row, ⟨point, hb, hr.symm ▸ mem_singleton row⟩, by simp [he, hr, wall]⟩
  · rintro ⟨row, ⟨point, hp, hr⟩, rfl⟩
    have hh := singleton_subset_iff.mpr hr
    refine ⟨sys.isFace_locus _, ⟨point, hp, hh⟩, ?_⟩
    rw [reg.dim_body ⟨point, hp⟩]
    simpa [wall, Nat.add_comm] using reg.dim_locus hp hh

theorem Regular.facet_count (reg : sys.Regular) :
    (facets sys.body).ncard = sys.used.ncard := by
  rw [reg.facets_eq, reg.injOn_wall.ncard_image]

theorem Regular.simple (reg : sys.Regular) : Simple sys.body := by
  intro point hv
  have hs : sys.active point ⊆ sys.used := fun _ hr => ⟨point, hv.1, hr⟩
  have he : {face ∈ facets sys.body | point ∈ face} = sys.wall '' sys.active point := by
    rw [reg.facets_eq]
    ext face
    constructor
    · rintro ⟨⟨row, _, rfl⟩, _, hh⟩
      exact ⟨row, hh (mem_singleton row), rfl⟩
    · rintro ⟨row, hr, rfl⟩
      exact ⟨⟨row, hs hr, rfl⟩, hv.1, singleton_subset_iff.mpr hr⟩
  rw [he, (reg.injOn_wall.mono hs).ncard_image, (reg.vertex_card hv.1).mp hv,
    reg.dim_body ⟨point, hv.1⟩]

end OAI.Geometry.Hirsch.System

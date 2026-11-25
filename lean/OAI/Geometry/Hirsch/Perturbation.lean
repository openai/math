import OAI.Geometry.Hirsch.Padding
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

noncomputable section

open Set Module Filter
open scoped Topology

namespace OAI.Geometry.Hirsch

variable {Space Row Coord : Type} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [FiniteDimensional ℝ Space] [Fintype Row]

abbrev Data (Space Row : Type) [NormedAddCommGroup Space] [NormedSpace ℝ Space] :=
  (Row → Space →L[ℝ] ℝ) × (Row → ℝ)

namespace Data

def sys (data : Data Space Row) : System Space Row :=
  ⟨fun row => (data.1 row).toLinearMap, data.2⟩

def ofSystem (sys : System Space Row) : Data Space Row :=
  (fun row => LinearMap.toContinuousLinearMap (sys.normal row), sys.rhs)

def consistent (normals : Row → Space →L[ℝ] ℝ) (rows : Set Row) :
    Submodule ℝ (Row → ℝ) where
  carrier := {rhs | ∃ point, ∀ row ∈ rows, normals row point = rhs row}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨first, hf⟩ ⟨last, hl⟩
    exact ⟨first + last, fun row hr => by simp [hf row hr, hl row hr]⟩
  smul_mem' := by
    rintro scale _ ⟨point, hp⟩
    exact ⟨scale • point, fun row hr => by simp [hp row hr]⟩

theorem dense_rational_vector (Index : Type) :
    Dense {vec : Index → ℝ | ∀ idx, ∃ rat : ℚ, vec idx = rat} := by
  have hd := DenseRange.piMap (fun _ : Index => (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)))
  apply hd.mono
  rintro _ ⟨vec, rfl⟩ idx
  exact ⟨vec idx, rfl⟩

omit [FiniteDimensional ℝ Space] in
theorem dense_regular_rhs (normals : Row → Space →L[ℝ] ℝ) :
    Dense {rhs | (sys (normals, rhs)).Regular ∧ ∀ row, ∃ rat : ℚ, rhs row = rat} := by
  let bad := {rows | consistent normals rows ≠ ⊤}
  let avoid := fun rows : bad => (consistent normals rows.val : Set (Row → ℝ))ᶜ
  have ho : ∀ rows, IsOpen (avoid rows) :=
    fun rows => (consistent normals rows.val).closed_of_finiteDimensional.isOpen_compl
  have hd : ∀ rows, Dense (avoid rows) := by
    intro rows
    apply interior_eq_empty_iff_dense_compl.mp
    by_contra hn
    exact rows.property ((consistent normals rows.val).eq_top_of_nonempty_interior'
      (nonempty_iff_ne_empty.mpr hn))
  apply ((dense_iInter_of_isOpen ho hd).inter_of_isOpen_left (dense_rational_vector Row)
    (isOpen_iInter_of_finite ho)).mono
  rintro rhs ⟨hr, hrat⟩
  refine ⟨?_, hrat⟩
  intro point _ values
  let rows := (sys (normals, rhs)).active point
  have he : consistent normals rows = ⊤ := by
    by_contra hn
    exact mem_iInter.mp hr ⟨rows, hn⟩ ⟨point, fun row hh => hh⟩
  exact (show values ∈ consistent normals rows by rw [he]; trivial)

theorem dense_rational_normal [Fintype Coord] (basis : Basis Coord ℝ Space) :
    Dense {lin : Space →L[ℝ] ℝ | ∀ idx, ∃ rat : ℚ, lin (basis idx) = rat} := by
  let eqv := (basis.constr ℝ (M' := ℝ)).trans LinearMap.toContinuousLinearMap
  have hc := eqv.toLinearMap.continuous_of_finiteDimensional
  have hd := eqv.surjective.denseRange.dense_image hc (dense_rational_vector Coord)
  apply hd.mono
  rintro _ ⟨vec, hv, rfl⟩ idx
  change ∃ rat : ℚ, (basis.constr ℝ vec) (basis idx) = rat
  rw [Basis.constr_basis]
  exact hv idx

theorem exists_rational_regular [Fintype Coord] (basis : Basis Coord ℝ Space)
    {data : Data Space Row} {prop : Data Space Row → Prop} (he : ∀ᶠ other in 𝓝 data, prop other) :
    ∃ other, prop other ∧ other.sys.Regular ∧
      (∀ row coord, ∃ rat : ℚ, other.sys.normal row (basis coord) = rat) ∧
      (∀ row, ∃ rat : ℚ, other.sys.rhs row = rat) := by
  obtain ⟨left, hl, right, hr, hsub⟩ := mem_nhds_prod_iff.mp he
  have hd := dense_pi (Set.univ : Set Row) (fun _ _ => dense_rational_normal basis)
  obtain ⟨normals, hm, hn⟩ := mem_closure_iff_nhds.mp (hd data.1) left hl
  obtain ⟨rhs, hv, hreg, hrat⟩ :=
    mem_closure_iff_nhds.mp (dense_regular_rhs normals data.2) right hr
  exact ⟨(normals, rhs), hsub ⟨hm, hv⟩, hreg, fun row => hn row (mem_univ _), hrat⟩

def Strict (data : Data Space Row) (point : Space) : Prop :=
  ∀ row, data.2 row < data.1 row point

omit [FiniteDimensional ℝ Space] [Fintype Row] in
theorem Strict.mem {data : Data Space Row} {point : Space} (hp : data.Strict point) :
    point ∈ data.sys.body := fun row => (hp row).le

omit [FiniteDimensional ℝ Space] in
theorem Strict.eventually {data : Data Space Row} {point : Space} (hp : data.Strict point) :
    ∀ᶠ other in 𝓝 data, other.Strict point := by
  apply eventually_all.mpr
  intro row
  exact (isOpen_lt (by fun_prop) (by fun_prop) :
    IsOpen {other : Data Space Row | other.2 row < other.1 row point}).mem_nhds (hp row)

omit [FiniteDimensional ℝ Space] [Fintype Row] in
theorem closed_body {Param : Type} [TopologicalSpace Param]
    {get : Param → Data Space Row} {point : Param → Space}
    (hg : Continuous get) (hp : Continuous point) :
    IsClosed {param | point param ∈ (get param).sys.body} := by
  change IsClosed {param | ∀ row, (get param).2 row ≤ (get param).1 row (point param)}
  rw [ofPred_forall]
  exact isClosed_iInter fun row => isClosed_le (by fun_prop) (by fun_prop)

theorem uniform_compact {data : Data Space Row} (hc : IsCompact data.sys.body)
    {point : Space} (hp : data.Strict point) :
    ∃ box : Set Space, IsCompact box ∧ ∀ᶠ other in 𝓝 data, other.sys.body ⊆ box := by
  obtain ⟨radius, hb⟩ := hc.isBounded.subset_ball point
  have hr : 0 < radius := by simpa using hb hp.mem
  have hev : ∀ᶠ other in 𝓝 data, ∀ pt ∈ Metric.sphere point radius, pt ∉ other.sys.body := by
    apply (isCompact_sphere point radius).eventually_forall_of_forall_eventually
    intro pt ht
    apply (closed_body continuous_fst continuous_snd).isOpen_compl.mem_nhds
    intro hh
    exact (Metric.mem_ball.mp (hb hh)).ne (Metric.mem_sphere.mp ht)
  refine ⟨Metric.closedBall point radius, isCompact_closedBall _ _, ?_⟩
  filter_upwards [hev, hp.eventually] with other ho hw pt ht
  by_contra hn
  have hh : radius ≤ dist pt point := (not_le.mp hn).le
  obtain ⟨mid, hm, he⟩ := other.sys.convex_body.isPreconnected.intermediate_value hw.mem ht
    (show ContinuousOn (fun mid => dist mid point) _ from (continuous_id.dist continuous_const).continuousOn)
    ⟨by simpa using hr.le, hh⟩
  exact ho mid he hm

end Data
end OAI.Geometry.Hirsch

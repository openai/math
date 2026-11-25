import OAI.Geometry.Hirsch.Regular
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.Prod

noncomputable section

open Set Module

namespace OAI.Geometry.Hirsch

variable {Space Row : Type} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [FiniteDimensional ℝ Space]

abbrev Vertex (body : Set Space) := ↥(body.extremePoints ℝ)

def graph (body : Set Space) (moves : ℕ) : SimpleGraph (Vertex body) where
  Adj first last := first ≠ last ∧ ∃ face, IsFace body face ∧ dim face ≤ moves ∧
    first.val ∈ face ∧ last.val ∈ face
  symm := ⟨by rintro _ _ ⟨hn, face, hf, hd, hx, hy⟩; exact ⟨hn.symm, face, hf, hd, hy, hx⟩⟩
  loopless := ⟨fun _ hh => hh.1 rfl⟩

theorem edge_iff {body : Set Space} {first last : Vertex body} :
    (graph body 1).Adj first last ↔ first ≠ last ∧
      ∃ face, IsFace body face ∧ dim face = 1 ∧ first.val ∈ face ∧ last.val ∈ face := by
  constructor
  · rintro ⟨hn, face, hf, hd, hx, hy⟩
    have hne : dim face ≠ 0 := by
      intro hz
      have he := (vectorSpan_eq_bot_iff_subsingleton ℝ).mp (Submodule.finrank_eq_zero.mp hz)
      exact hn (Subtype.ext (he hx hy))
    exact ⟨hn, face, hf, by omega, hx, hy⟩
  · rintro ⟨hn, face, hf, hd, hx, hy⟩
    exact ⟨hn, face, hf, hd.le, hx, hy⟩

omit [FiniteDimensional ℝ Space] in
theorem graph_mono (body : Set Space) {small large : ℕ} (hm : small ≤ large) :
    graph body small ≤ graph body large := by
  rintro _ _ ⟨hn, face, hf, hd, hx, hy⟩
  exact ⟨hn, face, hf, hd.trans hm, hx, hy⟩

theorem vertex_max {body : Set Space} (hc : IsCompact body) (hne : body.Nonempty)
    (obj : Space →ₗ[ℝ] ℝ) :
    ∃ vertex : Vertex body, ∀ point ∈ body, obj point ≤ obj vertex.val := by
  let lin := LinearMap.toContinuousLinearMap obj
  have he := ContinuousLinearMap.toExposed.isExposed (l := lin) (A := body)
  obtain ⟨point, hp, hm⟩ := hc.exists_isMaxOn hne lin.continuous.continuousOn
  obtain ⟨best, hb⟩ := (he.isCompact hc).extremePoints_nonempty ⟨point, hp, hm⟩
  exact ⟨⟨best, he.isExtreme.extremePoints_subset_extremePoints hb⟩, hb.1.2⟩

namespace System

variable {sys : System Space Row}

theorem compact_locus (hc : IsCompact sys.body) (rows : Set Row) :
    IsCompact (sys.locus rows) := by
  have he : sys.locus rows = sys.body ∩ ⋂ row ∈ rows, {p | sys.normal row p = sys.rhs row} := by
    ext point
    simp [locus, active, subset_def]
  rw [he]
  exact hc.inter_right (isClosed_iInter fun row => isClosed_iInter fun _ =>
    isClosed_eq (sys.normal row).continuous_of_finiteDimensional continuous_const)

variable [Finite Row]

theorem Regular.improving_edge (reg : sys.Regular) (hc : IsCompact sys.body)
    (obj : Space →ₗ[ℝ] ℝ) (start : Vertex sys.body) {target : Space}
    (ht : target ∈ sys.body) (hi : obj start.val < obj target) :
    ∃ finish, (graph sys.body 1).Adj start finish ∧ obj start.val < obj finish.val := by
  classical
  let rows := sys.active start.val
  let := Fintype.ofFinite rows
  choose dir hd using fun pivot : rows => reg start.val start.property.1
    (fun row => if row = pivot.val then sys.normal row (target - start.val) else 0)
  have he : ∑ pivot, dir pivot = target - start.val := by
    apply sub_eq_zero.mp
    have hz : (∑ pivot, dir pivot) - (target - start.val) ∈ sys.directions rows := by
      refine sys.mem_directions.mpr fun row hr => ?_
      rw [map_sub, map_sum, Finset.sum_eq_single (⟨row, hr⟩ : rows)]
      · simp [hd _ row hr]
      · intro other _ hn
        rw [hd _ row hr, ite_eq_right (fun eqn => hn (Subtype.ext eqn.symm))]
      · simp
    rw [show sys.directions rows = ⊥ from (vertex_iff start.property.1).mp start.property] at hz
    exact hz
  have hex : ∃ pivot, 0 < obj (dir pivot) := by
    by_contra! hn
    have hh := Finset.sum_nonpos (s := Finset.univ) (fun pivot _ => hn pivot)
    rw [← map_sum, he, map_sub] at hh
    linarith
  obtain ⟨pivot, himp⟩ := hex
  have hn : ∀ row ∈ rows, 0 ≤ sys.normal row (dir pivot) := by
    intro row hr
    rw [hd pivot row hr]
    split
    · rw [map_sub, show sys.normal row start.val = _ from hr]
      exact sub_nonneg.mpr (ht row)
    · exact le_rfl
  obtain ⟨scale, hs, hp, ha⟩ := step start.property.1 hn
  let keep := rows \ {pivot.val}
  have hstart : start.val ∈ sys.locus keep := ⟨start.property.1, sdiff_subset⟩
  have hpoint : start.val + scale • dir pivot ∈ sys.locus keep := by
    refine ⟨hp, ?_⟩
    rw [ha]
    intro row hr
    exact ⟨hr.1, (hd pivot row hr.1).trans (ite_eq_right hr.2)⟩
  obtain ⟨best, hb⟩ := vertex_max (compact_locus hc keep) ⟨_, hpoint⟩ obj
  have hf := sys.isFace_locus keep
  let finish : Vertex sys.body := ⟨best.val, hf.extreme.extremePoints_subset_extremePoints best.property⟩
  have hlt : obj start.val < obj finish.val := by
    apply lt_of_lt_of_le _ (hb _ hpoint)
    rw [map_add, map_smul, smul_eq_mul]
    exact lt_add_of_pos_right _ (mul_pos hs himp)
  have hdim : dim (sys.locus keep) ≤ 1 := by
    have hh := reg.dim_locus start.property.1 hstart.2
    have hk : keep.ncard + 1 = rows.ncard := ncard_sdiff_singleton_add_one pivot.property
    have hv : rows.ncard = _ := (reg.vertex_card start.property.1).mp start.property
    omega
  exact ⟨finish, ⟨fun heq => hlt.ne (congrArg (fun v => obj v.val) heq),
    _, hf, hdim, hstart, best.property.1⟩, hlt⟩

theorem Regular.preconnected (reg : sys.Regular) (hc : IsCompact sys.body)
    {moves : ℕ} (hm : 1 ≤ moves) : (graph sys.body moves).Preconnected := by
  classical
  intro start target
  let rows := sys.active target.val
  let := Fintype.ofFinite rows
  let obj := -(∑ row : rows, sys.normal row)
  let reach := {v | (graph sys.body moves).Reachable start v}
  let : Finite (Vertex sys.body) := sys.finite_vertices.to_subtype
  obtain ⟨best, hb, hmax⟩ := exists_max_image reach (fun v => obj v.val) (toFinite reach)
    ⟨start, SimpleGraph.Reachable.refl _⟩
  have hle : obj target.val ≤ obj best.val := by
    by_contra! hn
    obtain ⟨next, hadj, hlt⟩ := reg.improving_edge hc obj best target.property.1 hn
    exact hlt.not_ge (hmax next (hb.trans ((graph_mono _ hm) hadj).reachable))
  have hh : ∀ row : rows, sys.normal row target.val ≤ sys.normal row best.val := by
    intro row
    rw [show sys.normal row target.val = _ from row.property]
    exact best.property.1 row
  have he : ∑ row : rows, sys.normal row target.val = ∑ row : rows, sys.normal row best.val :=
    le_antisymm (Finset.sum_le_sum (fun row _ => hh row))
      (by simpa [obj, LinearMap.sum_apply] using hle)
  have hsub : rows ⊆ sys.active best.val := by
    intro row hr
    have heq := (Finset.sum_eq_sum_iff_of_le (fun row _ => hh row)).mp he
      (⟨row, hr⟩ : rows) (Finset.mem_univ _)
    exact heq.symm.trans hr
  have hd := sub_mem_directions (sys := sys) (first := target.val) Subset.rfl hsub
  rw [(vertex_iff target.property.1).mp target.property] at hd
  have heq : target = best := Subtype.ext (sub_eq_zero.mp hd)
  rwa [heq]

end System
end OAI.Geometry.Hirsch

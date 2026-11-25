import OAI.Geometry.Hirsch.Perturbation

noncomputable section

open Set Filter Module
open scoped Topology

namespace OAI.Geometry.Hirsch

variable {Space Param Row : Type} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [FiniteDimensional ℝ Space] [NormedAddCommGroup Param] [NormedSpace ℝ Param]
  [FiniteDimensional ℝ Param] [Fintype Row]

theorem generic_affine (lin : Param →ₗ[ℝ] Space) (base : Space) (sub : Submodule ℝ Space) :
    IsOpen {param | base + lin param ∈ sub → ∀ dir, lin dir ∈ sub} ∧
    Dense {param | base + lin param ∈ sub → ∀ dir, lin dir ∈ sub} := by
  by_cases hh : ∀ dir, lin dir ∈ sub
  · simp [hh]
  have he : {param | base + lin param ∈ sub → ∀ dir, lin dir ∈ sub} =
      ((fun param => base + lin param) ⁻¹' (sub : Set Space))ᶜ := by ext; simp [hh]
  rw [he]
  refine ⟨(sub.closed_of_finiteDimensional.preimage
    (continuous_const.add lin.continuous_of_finiteDimensional)).isOpen_compl, ?_⟩
  rw [← interior_eq_empty_iff_dense_compl]
  by_contra hn
  obtain ⟨pt, hp⟩ := nonempty_iff_ne_empty.mpr hn
  have hm := interior_subset hp
  change base + lin pt ∈ sub at hm
  have hev : ∀ᶠ dir in 𝓝 (0 : Param), base + lin (pt + dir) ∈ sub := by
    have ht : Tendsto (fun dir => pt + dir) (𝓝 (0 : Param)) (𝓝 pt) := by
      simpa using (continuous_const_add pt).tendsto (0 : Param)
    exact ht.eventually (mem_interior_iff_mem_nhds.mp hp)
  have hint : (interior (sub.comap lin : Set Param)).Nonempty := by
    refine ⟨0, mem_interior_iff_mem_nhds.mpr ?_⟩
    filter_upwards [hev] with dir hd
    rw [map_add, ← add_assoc] at hd
    simpa using sub.sub_mem hd hm
  have htop := (sub.comap lin).eq_top_of_nonempty_interior' hint
  exact hh (fun dir => show dir ∈ sub.comap lin by rw [htop]; trivial)

theorem generic_all {Index : Type} [Finite Index] {prop : Index → Param → Prop}
    (hh : ∀ idx, IsOpen {pt | prop idx pt} ∧ Dense {pt | prop idx pt}) :
    IsOpen {pt | ∀ idx, prop idx pt} ∧ Dense {pt | ∀ idx, prop idx pt} := by
  rw [ofPred_forall]
  exact ⟨isOpen_iInter_of_finite (fun idx => (hh idx).1),
    dense_iInter_of_isOpen (fun idx => (hh idx).1) (fun idx => (hh idx).2)⟩

namespace System

variable (sys : System Space Row)

def assign (rhs : Row → ℝ) : System Space Row := ⟨sys.normal, rhs⟩

def Generic (lin : Param →ₗ[ℝ] (Row → ℝ)) (rhs : Row → ℝ) : Prop :=
  ∀ rows : Set Row, (∃ pt, rows ⊆ (sys.assign rhs).active pt) →
    ∀ dir, ∃ shift, ∀ row ∈ rows, sys.normal row shift = lin dir row

theorem generic_assign (lin : Param →ₗ[ℝ] (Row → ℝ)) (base : Row → ℝ) :
    IsOpen {pt | sys.Generic lin (base + lin pt)} ∧ Dense {pt | sys.Generic lin (base + lin pt)} := by
  apply generic_all
  intro rows
  exact generic_affine lin base (Data.consistent (Data.ofSystem sys).1 rows)

omit [FiniteDimensional ℝ Space] [FiniteDimensional ℝ Param] [Fintype Row] in
theorem Generic.regular {sys : System Space Row} {lin : Param →ₗ[ℝ] (Row → ℝ)} {rhs}
    (hg : sys.Generic lin rhs) (hs : Function.Surjective lin) : (sys.assign rhs).Regular := by
  intro point _ values
  obtain ⟨dir, rfl⟩ := hs values
  exact hg _ ⟨point, Subset.rfl⟩ dir

omit [FiniteDimensional ℝ Param] in
theorem open_generic (lin : Param →ₗ[ℝ] (Row → ℝ)) : IsOpen {rhs | sys.Generic lin rhs} := by
  unfold Generic
  rw [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro rows
  let sub := Data.consistent (Data.ofSystem sys).1 rows
  change IsOpen {rhs | rhs ∈ sub → ∀ dir, lin dir ∈ sub}
  by_cases he : ∀ dir, lin dir ∈ sub
  · simp [he]
  · simp only [he, imp_false]
    exact sub.closed_of_finiteDimensional.isOpen_compl

omit [FiniteDimensional ℝ Space] [FiniteDimensional ℝ Param] [Fintype Row] in
theorem Generic.required {sys : System Space Row} {lin : Param →ₗ[ℝ] (Row → ℝ)} {rhs}
    (hg : sys.Generic lin rhs) {point : Space} {rows : Set Row}
    (hs : rows ⊆ (sys.assign rhs).active point) (hd : sys.directions rows = ⊥)
    {row : Row} (hr : row ∈ (sys.assign rhs).active point)
    (free : ∃ dir, lin dir row ≠ 0 ∧ ∀ other ≠ row, lin dir other = 0) : row ∈ rows := by
  by_contra hn
  obtain ⟨dir, hne, hf⟩ := free
  obtain ⟨delta, he⟩ := hg _ ⟨point, Subset.rfl⟩ dir
  have hz : delta ∈ sys.directions rows := sys.mem_directions.mpr fun other hh =>
    (he other (hs hh)).trans (hf other (fun eqn => hn (eqn ▸ hh)))
  rw [hd] at hz
  have hh := he row hr
  rw [show delta = 0 from hz, map_zero] at hh
  exact hne hh.symm

omit [FiniteDimensional ℝ Space] [Fintype Row] in
theorem determining (rows : Set Row) (hd : sys.directions rows = ⊥) :
    ∃ solve : (Row → ℝ) →ₗ[ℝ] Space, ∀ rhs point, rows ⊆ (sys.assign rhs).active point → solve rhs = point := by
  obtain ⟨inv, hi⟩ := (sys.evaluation rows).exists_leftInverse_of_injective (by rw [ker_evaluation, hd])
  refine ⟨inv.comp (LinearMap.funLeft ℝ ℝ Subtype.val), fun rhs point hh => ?_⟩
  have he : (fun row : rows => rhs row.val) = sys.evaluation rows point :=
    funext fun row => (hh row.property).symm
  change inv (fun row : rows => rhs row.val) = _
  rw [he]
  exact DFunLike.congr_fun hi point

theorem closed_determining (rows : Set Row) (hd : sys.directions rows = ⊥) :
    IsClosed {rhs | ((sys.assign rhs).locus rows).Nonempty} := by
  obtain ⟨solve, hs⟩ := sys.determining rows hd
  have he : {rhs | ((sys.assign rhs).locus rows).Nonempty} =
      {rhs | (∀ row, rhs row ≤ sys.normal row (solve rhs)) ∧
        ∀ row ∈ rows, sys.normal row (solve rhs) = rhs row} := by
    ext rhs
    constructor
    · rintro ⟨point, hp⟩
      change solve rhs ∈ (sys.assign rhs).locus rows
      rwa [hs rhs point hp.2]
    · exact fun hh => ⟨solve rhs, hh⟩
  rw [he]
  simp only [ofPred_and, ofPred_forall]
  have hc := fun row => (sys.normal row).continuous_of_finiteDimensional.comp solve.continuous_of_finiteDimensional
  exact (isClosed_iInter fun row => isClosed_le (continuous_apply row) (hc row)).inter
    (isClosed_iInter fun row => isClosed_iInter fun _ => isClosed_eq (hc row) (continuous_apply row))

theorem stable_patterns (rhs : Row → ℝ) : ∀ᶠ other in 𝓝 rhs,
    ∀ rows : Set Row, sys.directions rows = ⊥ → ((sys.assign other).locus rows).Nonempty →
      ((sys.assign rhs).locus rows).Nonempty := by
  apply eventually_all.mpr
  intro rows
  by_cases hd : sys.directions rows = ⊥
  swap
  · exact Eventually.of_forall (fun _ hh => (hd hh).elim)
  by_cases hh : ((sys.assign rhs).locus rows).Nonempty
  · exact Eventually.of_forall (fun _ _ _ => hh)
  filter_upwards [(sys.closed_determining rows hd).isOpen_compl.mem_nhds hh] with other hn _ he
  exact (hn he).elim

end System
end OAI.Geometry.Hirsch

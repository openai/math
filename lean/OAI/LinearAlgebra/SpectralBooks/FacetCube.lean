import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Coordinate cubes and their upper facets

At a relative interior point of a facet, each tangent line stays in that facet
for all sufficiently small positive and negative parameters.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Set
open scoped Topology InnerProductSpace

section

variable {ι : Type*} [Fintype ι]

/-- The cube `[-a,a]^ι` in Euclidean coordinates. -/
def coordinateCube (ι : Type*) (a : ℝ) : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ j, x j ∈ Icc (-a) a}

/-- The upper facet of the unit cube perpendicular to the indicated axis. -/
def upperUnitCubeFacet (i : ι) : Set (EuclideanSpace ℝ ι) :=
  {x | x ∈ coordinateCube ι 1 ∧ x i = 1}

/-- The common unit cube sits in the interior of the doubled cube. -/
theorem coordinateCube_one_subset_interior_two :
    coordinateCube ι 1 ⊆ interior (coordinateCube ι 2) := by
  intro p hp
  apply mem_interior_iff_mem_nhds.mpr
  change ∀ᶠ x in 𝓝 p, ∀ j, x j ∈ Icc (-2 : ℝ) 2
  apply eventually_all.mpr
  intro j
  have hc := (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.continuousAt (x := p)
  have hj := hp j
  have hmem : p j ∈ Ioo (-2 : ℝ) 2 :=
    ⟨lt_of_lt_of_le (by norm_num) hj.1, lt_of_le_of_lt hj.2 (by norm_num)⟩
  have hnear : ∀ᶠ x in 𝓝 p, x j ∈ Ioo (-2 : ℝ) 2 := hc (Ioo_mem_nhds hmem.1 hmem.2)
  exact hnear.mono fun _ hx ↦ Ioo_subset_Icc_self hx

variable [DecidableEq ι]

/-- If the charts agree on the unit facet, the distance in either chart
has the Euclidean value along each small tangent segment in that facet. -/
theorem eventually_tangent_line_facet_distance
    {C : Set (EuclideanSpace ℝ ι)} {f : EuclideanSpace ℝ ι → ℝ}
    {p : EuclideanSpace ℝ ι} {r : ℝ} {i : ι}
    (hC : coordinateCube ι 1 ⊆ C) (hn : p i = 1)
    (ht : ∀ j, j ≠ i → p j ∈ Ioo (-1 : ℝ) 1)
    (hf : ∀ x ∈ upperUnitCubeFacet i, f x = ‖x - (p + r • EuclideanSpace.single i 1)‖) :
    ∀ v : EuclideanSpace ℝ ι, ⟪v, EuclideanSpace.single i 1⟫_ℝ = 0 →
      ∀ᶠ t : ℝ in 𝓝 0, p + t • v ∈ C ∧
        f (p + t • v) = ‖(p + t • v) - (p + r • EuclideanSpace.single i 1)‖ := by
  intro v hv
  have hvi : v i = 0 := by simpa [EuclideanSpace.inner_single_right] using hv
  have normal (t : ℝ) : (p + t • v) i = 1 := by
    simp [PiLp.add_apply, PiLp.smul_apply, hvi, hn]
  have hcube : ∀ᶠ t : ℝ in 𝓝 0, p + t • v ∈ coordinateCube ι 1 := by
    apply eventually_all.mpr
    intro j
    by_cases h : j = i
    · subst j
      exact Eventually.of_forall fun t ↦ by simp [normal]
    · have hc : ContinuousAt (fun t : ℝ ↦ p j + t * v j) 0 :=
        continuous_const.continuousAt.add (continuousAt_id.mul continuousAt_const)
      have h0 : p j + 0 * v j ∈ Ioo (-1 : ℝ) 1 := by simpa using ht j h
      have hnear : ∀ᶠ t : ℝ in 𝓝 0, p j + t * v j ∈ Ioo (-1 : ℝ) 1 :=
        hc (Ioo_mem_nhds h0.1 h0.2)
      exact hnear.mono fun _ hx ↦ Ioo_subset_Icc_self hx
  filter_upwards [hcube] with t ht
  exact ⟨hC ht, hf _ ⟨ht, normal t⟩⟩

omit [Fintype ι] [DecidableEq ι] in
/-- A coordinate cube is compact in its Euclidean metric. -/
theorem isCompact_coordinateCube (a : ℝ) : IsCompact (coordinateCube ι a) := by
  have hc : IsCompact {x : ι → ℝ | ∀ j, x j ∈ Icc (-a) a} :=
    isCompact_pi_infinite fun _ ↦ isCompact_Icc
  have h := hc.image (PiLp.continuous_toLp 2 (fun _ : ι ↦ ℝ))
  convert! h using 1
  ext x
  exact ⟨fun hx ↦ ⟨x.ofLp, hx, rfl⟩, fun ⟨_, hx, h⟩ ↦ h ▸ hx⟩

omit [Fintype ι] in
/-- Extending any point of the upper facet upwards by at most one stays in the
doubled cube. -/
theorem outward_tip_mem_coordinateCube_two {i : ι} {p : EuclideanSpace ℝ ι}
    (hp : p ∈ upperUnitCubeFacet i) {r : ℝ} (hr : r ∈ Icc 0 1) :
    p + r • EuclideanSpace.single i 1 ∈ coordinateCube ι 2 := by
  intro j
  have hj := hp.1 j
  by_cases heq : j = i
  · subst j
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_true,
      smul_eq_mul, mul_one, hp.2, mem_Icc]
    constructor <;> linarith [hr.1, hr.2]
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_eq_right_iff.mpr (fun h ↦ (heq h).elim),
      smul_zero, add_zero]
    exact Icc_subset_Icc (by norm_num) (by norm_num) hj

/-- Approximate a boundary foot by feet in the relative interior of its facet. -/
theorem exists_seq_in_facet_relative_interior {i : ι} {p : EuclideanSpace ℝ ι}
    (hp : p ∈ upperUnitCubeFacet i) :
    ∃ u : ℕ → EuclideanSpace ℝ ι, Tendsto u atTop (𝓝 p) ∧
      ∀ n, u n ∈ upperUnitCubeFacet i ∧ ∀ j, j ≠ i → u n j ∈ Ioo (-1 : ℝ) 1 := by
  let a (n : ℕ) : ℝ := 1 / (n + 1)
  let e := EuclideanSpace.single i (1 : ℝ)
  let u (n : ℕ) := a n • e + (1 - a n) • p
  have ha : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨u, ?_, fun n ↦ ?_⟩
  · simpa [u] using (ha.smul (tendsto_const_nhds (x := e))).add
      ((tendsto_const_nhds (x := (1 : ℝ))).sub ha |>.smul (tendsto_const_nhds (x := p)))
  · have ha0 : 0 < a n := by dsimp [a]; positivity
    have ha1 : a n ≤ 1 := by dsimp [a]; rw [div_le_one (by positivity)]; norm_cast; omega
    have normal : u n i = 1 := by
      simp [u, e, PiLp.add_apply, PiLp.smul_apply, hp.2]
    have ht j (hj : j ≠ i) : u n j ∈ Ioo (-1 : ℝ) 1 := by
      have h := hp.1 j
      simp only [u, e, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
        ite_eq_right_iff.mpr (fun h ↦ (hj h).elim), smul_eq_mul, mem_Ioo]
      constructor
      · linarith [mul_le_mul_of_nonneg_left h.1 (sub_nonneg.mpr ha1)]
      · linarith [mul_le_mul_of_nonneg_left h.2 (sub_nonneg.mpr ha1)]
    refine ⟨⟨fun j ↦ ?_, normal⟩, ht⟩
    by_cases hj : j = i
    · simp [hj, normal]
    · exact Ioo_subset_Icc_self (ht j hj)

end

end SpectralBooks
end LinearAlgebra
end OAI

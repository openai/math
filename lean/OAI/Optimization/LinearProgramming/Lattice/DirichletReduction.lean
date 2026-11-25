import OAI.Optimization.LinearProgramming.Lattice.DirichletGraph
import OAI.Optimization.LinearProgramming.Lattice.LLL

/-! From the short-prefix property of a reduced basis to the simultaneous approximation
used by sign-preserving rounding in Appendix A. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

/-- The first row is `(α,u)`; the remaining rows are the negatives of the last coordinate rows. -/
noncomputable def graphGenerators {p : ℕ} (α : ℝ) (u : Fin p → ℝ) :
    Fin (p + 1) → EuclideanSpace ℝ (Fin (p + 1)) :=
  Fin.cons (graphVector α u 1 0) (fun i ↦ graphVector α u 0 (fun j ↦ if i = j then 1 else 0))

private theorem graphGenerators_sum_apply {p : ℕ} (α : ℝ) (u : Fin p → ℝ)
    (a : Fin (p+1) → ℝ) (j : Fin (p+1)) :
    (∑ i, a i • graphGenerators α u i) j = ∑ i, a i * graphGenerators α u i j := by
  let proj := PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin (p+1) ↦ ℝ) j
  change proj (∑ i, a i • graphGenerators α u i) = _
  simp [proj, map_sum]

private theorem graphGenerators_sum_zero {p : ℕ} (α : ℝ) (u : Fin p → ℝ) (a : Fin (p+1) → ℝ) :
    (∑ i, a i • graphGenerators α u i) 0 = a 0 * α := by
  rw [graphGenerators_sum_apply, Fin.sum_univ_succ]
  simp [graphGenerators]

private theorem graphGenerators_sum_succ {p : ℕ} (α : ℝ) (u : Fin p → ℝ) (a : Fin (p+1) → ℝ)
    (j : Fin p) : (∑ i, a i • graphGenerators α u i) j.succ = a 0 * u j - a j.succ := by
  rw [graphGenerators_sum_apply, Fin.sum_univ_succ]
  simp [graphGenerators, apply_ite, sub_eq_add_neg]

/-- These explicit generators are independent for every nonzero scale. -/
theorem graphGenerators_independent {p : ℕ} {α : ℝ} (ha : α ≠ 0) (u : Fin p → ℝ) :
    LinearIndependent ℝ (graphGenerators α u) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a h i
  have h0 : a 0 = 0 := by
    have h0 := congrArg (fun y : EuclideanSpace ℝ (Fin (p+1)) ↦ y 0) h
    rw [graphGenerators_sum_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_right ha
  refine Fin.cases h0 (fun j ↦ ?_) i
  have hj := congrArg (fun y : EuclideanSpace ℝ (Fin (p+1)) ↦ y j.succ) h
  simpa [graphGenerators_sum_succ, h0] using hj

/-- Integer combinations of the displayed generators are exactly the graph lattice. -/
theorem graphVector_combination {p : ℕ} (α : ℝ) (u : Fin p → ℝ) (a : Fin (p+1) → ℤ) :
    (∑ i, a i • graphGenerators α u i) = graphVector α u (a 0) (fun i ↦ a i.succ) := by
  simp_rw [← Int.cast_smul_eq_zsmul ℝ]
  ext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · rw [graphGenerators_sum_zero, graphVector_zero_coord, mul_comm]
  · rw [graphGenerators_sum_succ, graphVector_succ_coord]

theorem mem_graphLattice_iff {p : ℕ} (α : ℝ) (u : Fin p → ℝ) (x : EuclideanSpace ℝ (Fin (p+1))) :
    x ∈ Submodule.span ℤ (Set.range (graphGenerators α u)) ↔
      ∃ q z, x = graphVector α u q z := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a 0, fun i ↦ a i.succ, graphVector_combination α u a⟩
  · rintro ⟨q, z, rfl⟩
    exact ⟨Fin.cons q z, graphVector_combination α u (Fin.cons q z)⟩

/-- Choosing a large enough grid gives the prescribed error for LLL's first graph basis vector. -/
theorem graph_reduced_first_short {p Q : ℕ} (hQ : 0 < Q) (u : Fin p → ℝ)
    (b : Fin (p+1) → EuclideanSpace ℝ (Fin (p+1))) (hi : LinearIndependent ℝ b)
    (hr : LLLReduced b)
    (hs : Submodule.span ℤ (Set.range b) =
      Submodule.span ℤ (Set.range (graphGenerators (1 / (Q : ℝ) ^ (p+1)) u))) :
    ‖b 0‖ ≤ (2 : ℝ) ^ (p + 1) * Real.sqrt (p + 1) / Q := by
  let α : ℝ := 1 / (Q : ℝ) ^ (p+1)
  obtain ⟨q,z,_,_,hne,hn⟩ := graph_short_witness hQ u
  let g := graphVector α u q z
  have hm : g ∈ Submodule.span ℤ (Set.range b) := by
    rw [hs]
    exact (mem_graphLattice_iff α u g).mpr ⟨q,z,rfl⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hm
  have hrep : g = ∑ i, (a i : ℝ) • b i := by simpa only [Int.cast_smul_eq_zsmul] using ha.symm
  obtain ⟨j,_,hb⟩ := lll_short_prefix hi hr a hrep hne
  calc
    _ ≤ (2 : ℝ)^(p+1) * ‖g‖ := hb 0 (Fin.zero_le j)
    _ ≤ (2 : ℝ)^(p+1) * (Real.sqrt (p+1)/Q) := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = _ := by ring

/-- The manuscript's concrete grid size suffices for the first-vector norm bound. -/
theorem graph_grid_sufficient (p : ℕ) {ε : ℝ} (hε : 0 < ε) {Q : ℕ}
    (hQ : (2 : ℝ) ^ (p+4) * (p+1) / ε ≤ Q) :
    (2 : ℝ) ^ (p+1) * Real.sqrt (p+1) ≤ (ε / 2) * Q := by
  have hbase : (0 : ℝ) ≤ (p : ℝ) + 1 := by positivity
  have hroot : Real.sqrt ((p : ℝ)+1) ≤ p+1 := (Real.sqrt_le_left hbase).mpr (by nlinarith [sq_nonneg (p : ℝ), Nat.cast_nonneg (α := ℝ) p])
  have h0 := (div_le_iff₀ hε).mp hQ
  have hp : (2 : ℝ)^(p+4) = 8 * 2^(p+1) := by rw [show p+4 = p+1+3 by omega, pow_add]; ring
  rw [hp] at h0
  nlinarith [mul_le_mul_of_nonneg_left hroot (show 0 ≤ (2 : ℝ)^(p+1) by positivity),
    mul_nonneg (show 0 ≤ (2 : ℝ)^(p+1) by positivity) hbase]

/-- The first row of any reduced basis of the graph lattice supplies a common positive denominator
and integer numerators meeting the approximation and size bounds of Appendix A. -/
theorem reducedGraph_approximates {p Q : ℕ} (hQ : 0 < Q) (u u' : Fin p → ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε' : ε ≤ 1) (hgrid : (2 : ℝ)^(p+4) * (p+1) / ε ≤ Q)
    (hu : ∀ i, |u i| ≤ 1) (hclose : ∀ i, |u i - u' i| ≤ 1 / (Q : ℝ)^(p+1))
    (b : Fin (p+1) → EuclideanSpace ℝ (Fin (p+1))) (hi : LinearIndependent ℝ b)
    (hr : LLLReduced b) (hs : Submodule.span ℤ (Set.range b) =
      Submodule.span ℤ (Set.range (graphGenerators (1 / (Q : ℝ)^(p+1)) u'))) :
    ∃ (d : ℕ) (w : Fin p → ℤ), 0 < d ∧ d ≤ (Q : ℝ)^(p+1) ∧
      (∀ i, |(d : ℝ) * u i - w i| ≤ ε) ∧ (∀ i, |w i| ≤ (d : ℤ) + 1) := by
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hbmem : b 0 ∈ Submodule.span ℤ (Set.range (graphGenerators (1 / (Q : ℝ)^(p+1)) u')) :=
    hs ▸ Submodule.subset_span (Set.mem_range_self 0)
  obtain ⟨q, z, hvec⟩ := (mem_graphLattice_iff _ _ _).mp hbmem
  have hne := hi.ne_zero 0
  have hbnd := (graph_reduced_first_short hQ u' b hi hr hs).trans
    ((div_le_iff₀ hQr).mpr (graph_grid_sufficient p hε hgrid))
  rw [hvec] at hne hbnd
  simpa only [one_div, inv_inv] using decode_short_graphVector u u' q z
    (by positivity : 0 < 1 / (Q : ℝ)^(p+1)) hε' hu hclose hne hbnd

end Lattice
end LinearProgramming
end Optimization
end OAI

import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Combining finitely many spectral inequalities

Clearing denominators gives a common right-hand side in a finite family of
comparisons. Taking powers and summing then turns the family into one strict
comparison, with the opposite inequality at every point of the given set.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators NNReal Topology
open Filter

section

/-- Suppose one point satisfies every strict comparison in a finite family,
while each member of a set of points reverses at least one. If the right-hand
sides are positive there, two semiring elements separate the point from the set. -/
theorem exists_separating_pair_of_finite {S J : Type*} [CommSemiring S] [Fintype J]
    (A B : J → S) (f : S →+* ℝ≥0) (G : Set (S →+* ℝ≥0))
    (hf : ∀ j, f (A j) < f (B j))
    (hpos : ∀ g ∈ G, ∀ j, 0 < g (B j))
    (hG : ∀ g ∈ G, ∃ j, g (B j) < g (A j)) :
    ∃ X Y : S, f X < f Y ∧ ∀ g ∈ G, g Y < g X := by
  classical
  let D := ∏ j, B j
  let C (j : J) := A j * ∏ i ∈ Finset.univ.erase j, B i
  have hD (j : J) : D = B j * ∏ i ∈ Finset.univ.erase j, B i :=
    (Finset.mul_prod_erase _ B (Finset.mem_univ j)).symm
  have hB (j : J) : 0 < f (B j) := zero_le.trans_lt (hf j)
  have hd : 0 < f D := by
    simp only [D, map_prod]
    exact Finset.prod_pos fun j _ ↦ hB j
  have hc (j : J) : f (C j) < f D := by
    rw [hD j]
    simp only [C, map_mul, map_prod]
    exact mul_lt_mul_of_pos_right (hf j) (Finset.prod_pos fun i _ ↦ hB i)
  have hlim : Tendsto (fun n : ℕ ↦ ∑ j, (f (C j) / f D) ^ n) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ fun j _ ↦
      NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ((div_lt_one hd).mpr (hc j))
  obtain ⟨n, hsum, hn⟩ := ((hlim.eventually_lt_const zero_lt_one).and
    (eventually_gt_atTop 0)).exists
  refine ⟨∑ j, (C j) ^ n, D ^ n, ?_, ?_⟩
  · simp only [map_sum, map_pow]
    apply (div_lt_one (pow_pos hd n)).mp
    simpa only [div_eq_mul_inv, mul_pow, inv_pow, Finset.sum_mul] using hsum
  · intro g hg
    obtain ⟨j, hj⟩ := hG g hg
    have hj' : g D < g (C j) := by
      rw [hD j]
      simp only [C, map_mul, map_prod]
      exact mul_lt_mul_of_pos_right hj (Finset.prod_pos fun i _ ↦ hpos g hg i)
    simp only [map_sum, map_pow]
    exact (pow_lt_pow_left₀ hj' zero_le hn.ne').trans_le
      (Finset.single_le_sum_of_canonicallyOrdered (f := fun i ↦ g (C i) ^ n) (Finset.mem_univ j))

end

end SpectralBooks
end LinearAlgebra
end OAI

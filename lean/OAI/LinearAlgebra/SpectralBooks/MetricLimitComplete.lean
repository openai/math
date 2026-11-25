import OAI.Geometry.HyperbolicGroups.MetricProduct

/-! # Completeness of the countable pointed ultralimit

A Cauchy sequence in a cofinal ultralimit converges by following increasingly
long finite lists of representatives on an ultrafilter-large set of indices.
The factor spaces need only be metric spaces.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Topology HyperbolicObstruction MetricLimit

/-- The separated metric ultralimit along any ultrafilter on the naturals
finer than the tail filter is complete. -/
theorem completeSpace_metricLimit {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ atTop)
    {X : ℕ → Type*} [∀ n, MetricSpace (X n)] {o : ∀ n, X n} :
    CompleteSpace (Space (U := U) (X := X) (o := o)) := by
  classical
  let b (j : ℕ) : ℝ := 1 / (j + 1)
  have hb (j : ℕ) : 0 < b j := by dsimp [b]; positivity
  apply Metric.complete_of_convergent_controlled_sequences b hb
  intro q hq
  choose r hr using fun j ↦ SeparationQuotient.surjective_mk (q j)
  have hd (i j : ℕ) (hij : i ≤ j) :
      ∀ᶠ n in (U : Filter ℕ), dist ((r i).val n) ((r j).val n) ≤ 2 * b i := by
    have h := tendsto_point_dist (r i) (r j)
    change Tendsto _ _ (𝓝 (dist (SeparationQuotient.mk (r i)) (SeparationQuotient.mk (r j)))) at h
    rw [hr, hr] at h
    exact (h.eventually_lt_const (by linarith [hq i i j le_rfl hij, hb i])).mono
      (fun _ ↦ le_of_lt)
  let Good (n k : ℕ) : Prop := ∀ i ∈ Finset.range (k+1), ∀ j ∈ Finset.range (k+1),
    i ≤ j → dist ((r i).val n) ((r j).val n) ≤ 2 * b i
  have hevent (k : ℕ) : ∀ᶠ n in (U : Filter ℕ), Good n k := by
    apply (Finset.eventually_all _).2
    intro i _
    apply (Finset.eventually_all _).2
    intro j _
    by_cases hij : i ≤ j
    · exact (hd i j hij).mono (fun _ hn _ ↦ hn)
    · exact Eventually.of_forall (fun _ h ↦ (hij h).elim)
  let diag (n : ℕ) := Nat.findGreatest (Good n) n
  have hg (n : ℕ) : Good n (diag n) := by
    apply Nat.findGreatest_spec (Nat.zero_le _)
    simp [Good, mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (hb 0).le]
  have hdiag (i : ℕ) : ∀ᶠ n in (U : Filter ℕ), i ≤ diag n := by
    filter_upwards [hU (eventually_ge_atTop i), hevent i] with n hin hgood
    exact Nat.le_findGreatest hin hgood
  obtain ⟨R, hR⟩ := (r 0).bound
  let x : Bounded U X o := ⟨fun n ↦ (r (diag n)).val n, R + 2 * b 0, fun n ↦
    (dist_triangle _ ((r 0).val n) _).trans (add_le_add (hR n)
      (hg n 0 (by simp) (diag n) (by simp) (Nat.zero_le _)))⟩
  have hclose (i : ℕ) : dist (q i) (point x) ≤ 2 * b i := by
    rw [← hr i]
    apply le_of_tendsto (tendsto_point_dist (r i) x)
    filter_upwards [hdiag i] with n hn
    exact hg n i (Finset.mem_range.mpr (by omega)) (diag n) (by simp) hn
  refine ⟨point x, Metric.tendsto_nhds.mpr (fun ε hε ↦ ?_)⟩
  have hlim : Tendsto (fun n ↦ 2 * b n) atTop (𝓝 0) := by
    simpa [b] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  exact (hlim.eventually_lt_const hε).mono (fun i hi ↦ (hclose i).trans_lt hi)

end SpectralBooks
end LinearAlgebra
end OAI

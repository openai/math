import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Independent height optimization at endpoint wire loads

In the proof of the Student bound, each interior load gives an attained
one-variable optimum. A zero load requires heights tending to zero. A load
equal to the log-rank can be decreased and recovered by continuity.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Set
open scoped Topology

/-- Optimize each positive height independently. Sites whose optimum is
attained only in the limit at zero use the same vanishing auxiliary height. -/
private theorem sum_le_of_height_choices {ι : Type*} [Fintype ι]
    {m gain : ι → ℝ} {cost : ℝ → ℝ} {C : ℝ}
    (hheight : ∀ a : ι → ℝ, (∀ i, 0 < a i) →
      ∑ i, a i * m i ≤ C + ∑ i, cost (a i))
    (hzero : Tendsto cost (𝓝[>] 0) (𝓝 0))
    (hgainzero : ∀ i, m i = 0 → gain i = 0)
    (hgain : ∀ i, m i ≠ 0 → ∃ a > 0, gain i ≤ a * m i - cost a) :
    ∑ i, gain i ≤ C := by
  classical
  have aux (i : ι) : ∃ (a : ℝ → ℝ) (v : ℝ), gain i ≤ v ∧ (∀ t > 0, 0 < a t) ∧
      Tendsto (fun t ↦ a t * m i - cost (a t)) (𝓝[>] 0) (𝓝 v) := by
    by_cases hi : m i = 0
    · refine ⟨id, 0, (hgainzero i hi).le, fun t ht ↦ ht, ?_⟩
      simpa [hi] using hzero.neg
    · obtain ⟨a, ha, hva⟩ := hgain i hi
      exact ⟨fun _ ↦ a, _, hva, fun _ _ ↦ ha, tendsto_const_nhds⟩
  choose a v hv ha hlim using aux
  apply (Finset.sum_le_sum fun i _ ↦ hv i).trans
  apply le_of_tendsto (tendsto_finsetSum _ fun i _ ↦ hlim i)
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Finset.sum_sub_distrib]
  linarith [hheight (fun i ↦ a i t) (fun i ↦ ha i t ht)]

/-- The independent height inequality and the interior one-variable optimum
imply the sum of tails bound for all loads between zero and the log-rank.
Only continuity of the tail as a function of load at the upper endpoint is used. -/
theorem student_bound_of_height {ι : Type*} [Fintype ι]
    {m : ι → ℝ} {cost tailAtLoad : ℝ → ℝ} {C L : ℝ}
    (hC : 0 < C) (hL : 0 < L) (hm : ∀ i, 0 ≤ m i) (hmL : ∀ i, m i ≤ L)
    (hheight : ∀ a : ι → ℝ, (∀ i, 0 < a i) →
      ∑ i, a i * m i ≤ C + ∑ i, cost (a i))
    (hzero : Tendsto cost (𝓝[>] 0) (𝓝 0))
    (hopt : ∀ x, 0 < x → x < L → ∃ a > 0, C * tailAtLoad x ≤ a * x - cost a)
    (hcont : ContinuousWithinAt tailAtLoad (Iio L) L) :
    ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < m i), tailAtLoad (m i) ≤ 1 := by
  classical
  let s := Finset.univ.filter (fun i ↦ 0 < m i)
  let load (x : ℝ) (i : ι) := if m i = L then x else m i
  have hlim (i : ι) : Tendsto (fun x ↦ tailAtLoad (load x i))
      (𝓝[<] L) (𝓝 (tailAtLoad (m i))) := by
    by_cases hi : m i = L
    · simpa [load, hi] using hcont.tendsto
    · simp [load, hi]
  apply le_of_tendsto (tendsto_finsetSum s fun i _ ↦ hlim i)
  filter_upwards [Ioo_mem_nhdsLT hL] with x hx
  have hle (i : ι) : load x i ≤ m i := by
    by_cases hi : m i = L <;> simp [load, hi, hx.2.le]
  have hlt (i : ι) : load x i < L := by
    by_cases hi : m i = L
    · simpa [load, hi] using hx.2
    · simpa [load, hi] using lt_of_le_of_ne (hmL i) hi
  have hpos (i : ι) : 0 < load x i ↔ 0 < m i := by
    by_cases hi : m i = L <;> simp [load, hi, hL, hx.1]
  have hnonneg (i : ι) : 0 ≤ load x i := by
    by_cases hi : m i = L <;> simp [load, hi, hx.1.le, hm i]
  let g i := if 0 < m i then C * tailAtLoad (load x i) else 0
  have hsum : ∑ i, g i ≤ C := by
    apply sum_le_of_height_choices (m := load x) (cost := cost) _ hzero
    · intro i hi
      have hn : ¬ 0 < m i := fun h ↦ (ne_of_gt ((hpos i).2 h)) hi
      simp [g, hn]
    · intro i hi
      have hp := lt_of_le_of_ne (hnonneg i) (Ne.symm hi)
      simpa [g, (hpos i).1 hp] using hopt _ hp (hlt i)
    · intro a ha
      exact (Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hle i) (ha i).le).trans
        (hheight a ha)
  apply (mul_le_mul_iff_right₀ hC).mp
  simpa [g, s, Finset.mul_sum, Finset.sum_filter] using hsum

end SpectralBooks
end LinearAlgebra
end OAI

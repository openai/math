import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Tactic

/-!
# Comparing affine chords with parallel displacements

Contract one chord toward a center chosen to land its initial point at the
interior base of the other chord. At a sufficiently small scale this center
lies in the parameter domain, so Busemann convexity compares the two speeds.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set Filter
open scoped Topology

variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {C : Set E} (H : E → X)
    (hseg : ∀ p ∈ C, ∀ q ∈ C, ∀ t : ℝ, t ∈ Icc 0 1 →
      dist (H p) (H ((1 - t) • p + t • q)) = t * dist (H p) (H q))
    (hcon : ∀ z ∈ C, ∀ p ∈ C, ∀ q ∈ C, ∀ t : ℝ, t ∈ Icc 0 1 →
      dist (H ((1-t) • z + t • p)) (H ((1-t) • z + t • q)) ≤ t * dist (H p) (H q))

include hseg hcon

/-- Comparing proportional chords when the chord on the left starts in the interior. -/
theorem convex_chord_dist_le {p q r s : E} (hp : p ∈ interior C)
    (hq : q ∈ C) (hr : r ∈ C) (hs : s ∈ C) {c : ℝ} (hc : 0 < c)
    (he : q - p = c • (s - r)) : dist (H p) (H q) ≤ c * dist (H r) (H s) := by
  let z (t : ℝ) := (1-t)⁻¹ • (p - t • r)
  have hcont : ContinuousAt z 0 := by dsimp [z]; fun_prop (disch := norm_num)
  have hz : ∀ᶠ t in 𝓝[>] (0 : ℝ), z t ∈ C := by
    apply eventually_nhdsWithin_of_eventually_nhds
    apply hcont (mem_interior_iff_mem_nhds.1 ?_)
    simpa [z] using hp
  have ht₁ : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds zero_lt_one)
  have htc : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < c :=
    eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hc)
  have ht₀ : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t,hz,ht₁,htc,ht₀⟩ := (hz.and (ht₁.and (htc.and ht₀))).exists
  have hbase : (1-t) • z t + t • r = p := by
    simp [z, smul_smul, sub_ne_zero.mpr ht₁.ne']
  have htI : t / c ∈ Icc 0 1 := ⟨div_nonneg ht₀.le hc.le, (div_le_one hc).2 htc.le⟩
  have htq : (t / c) • (q - p) = t • (s - r) := by
    rw [he, smul_smul, div_mul_cancel₀ _ hc.ne']
  have hend : (1-t) • z t + t • s = (1 - t/c) • p + (t/c) • q := by
    calc
      (1-t) • z t + t • s = ((1-t) • z t + t • r) + t • (s-r) := by rw [smul_sub]; abel
      _ = p + (t / c) • (q - p) := by rw [hbase, htq]
      _ = _ := by rw [smul_sub, sub_smul, one_smul]; abel
  have h := hcon (z t) hz r hr s hs t ⟨ht₀.le,ht₁.le⟩
  rw [hbase, hend, hseg p (interior_subset hp) q hq _ htI] at h
  have h' := mul_le_mul_of_nonneg_left h hc.le
  rw [← mul_assoc, mul_div_cancel₀ _ hc.ne'] at h'
  apply le_of_mul_le_mul_left _ ht₀
  convert h' using 1
  ring

/-- Proportional chords with both bases in the interior have equal rescaled lengths. -/
theorem convex_chord_dist_eq {p q r s : E} (hp : p ∈ interior C)
    (hq : q ∈ C) (hr : r ∈ interior C) (hs : s ∈ C) {c : ℝ} (hc : 0 < c)
    (he : q - p = c • (s-r)) : dist (H p) (H q) = c * dist (H r) (H s) := by
  refine le_antisymm (convex_chord_dist_le H hseg hcon hp hq (interior_subset hr) hs hc he) ?_
  have he' : s - r = c⁻¹ • (q-p) := by rw [he, inv_smul_smul₀ hc.ne']
  have h := convex_chord_dist_le H hseg hcon hr hs (interior_subset hp) hq (inv_pos.mpr hc) he'
  simpa only [mul_inv_cancel_left₀ hc.ne'] using mul_le_mul_of_nonneg_left h hc.le

end SpectralBooks
end LinearAlgebra
end OAI

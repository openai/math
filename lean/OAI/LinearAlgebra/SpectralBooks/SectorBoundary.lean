import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# Extending a seminorm description from the interior

Moving both endpoints toward a fixed interior point gives interior chords.
Their image endpoints tend to the original endpoints by the constant-speed law.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Set
open scoped Topology

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace X]

/-- An affine constant-speed map on a convex set with nonempty interior inherits
the interior seminorm distance formula on every chord of the set. -/
theorem convex_chord_dist_boundary {C : Set E} (hC : Convex ℝ C)
    (hI : (interior C).Nonempty) (H : E → X)
    (hseg : ∀ p ∈ C, ∀ q ∈ C, ∀ t : ℝ, t ∈ Icc 0 1 →
      dist (H p) (H ((1-t) • p + t • q)) = t * dist (H p) (H q))
    (N : Seminorm ℝ E) (hN : ∀ p ∈ interior C, ∀ q ∈ interior C,
      dist (H p) (H q) = N (p-q)) :
    ∀ p ∈ C, ∀ q ∈ C, dist (H p) (H q) = N (p-q) := by
  obtain ⟨o, ho⟩ := hI
  let chord (x : E) (t : ℝ) := (1-t) • x + t • o
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 1 := Ioo_mem_nhdsGT zero_lt_one
  have hzero : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hlim (x : E) (hx : x ∈ C) :
      Tendsto (fun t ↦ H (chord x t)) (𝓝[>] 0) (𝓝 (H x)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have h := hzero.mul_const (dist (H x) (H o))
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [hsmall] with t ht
    exact (hseg x hx o (interior_subset ho) t ⟨ht.1.le, ht.2.le⟩).symm.trans (dist_comm _ _)
  have hint (x : E) (hx : x ∈ C) (t : ℝ) (ht : t ∈ Ioo 0 1) :
      chord x t ∈ interior C :=
    hC.openSegment_self_interior_subset_interior hx ho
      ⟨1-t, t, sub_pos.mpr ht.2, ht.1, sub_add_cancel _ _, rfl⟩
  intro p hp q hq
  have hnorm := ((tendsto_const_nhds (x := (1 : ℝ))).sub hzero).mul_const (N (p-q))
  apply tendsto_nhds_unique ((hlim p hp).dist (hlim q hq))
  simp only [sub_zero, one_mul] at hnorm
  apply hnorm.congr'
  filter_upwards [hsmall] with t ht
  rw [hN _ (hint p hp t ht) _ (hint q hq t ht)]
  simp only [chord, add_sub_add_right_eq_sub, ← smul_sub, map_smul_eq_mul,
    Real.norm_of_nonneg (sub_nonneg.mpr ht.2.le)]

end SpectralBooks
end LinearAlgebra
end OAI

import OAI.Computability.VPVNP.WireGeodesic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Sequences

/-! # Midpoints in the completion of spectral wire geometry

The six-point transport inequality controls the displacement of midpoints
when their endpoints move. This makes midpoints of approximating endpoint
pairs a Cauchy sequence, as required in Corollary 2.5.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireGeometry

open Filter Set
open scoped Topology

/-- Exact midpoints pass through a dense isometry into a complete space if
midpoints in the source satisfy the fractional transport inequality. -/
theorem midpoints_of_dense_isometry {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompleteSpace Y] (f : X → Y) (hf : Isometry f) (hd : DenseRange f)
    (hmid : ∀ a b : X, ∃ z, AtFraction a b (1 / 2) z) (hT : FractionTransport X) :
    ∀ a b : Y, ∃ z, AtFraction a b (1 / 2) z := by
  intro a b
  have approx (y : Y) : ∃ x : ℕ → X, Tendsto (fun n ↦ f (x n)) atTop (𝓝 y) := by
    obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.mp (hd y)
    choose x hx using hw
    exact ⟨x, hlim.congr fun n ↦ (hx n).symm⟩
  obtain ⟨x, hx⟩ := approx a
  obtain ⟨y, hy⟩ := approx b
  choose mid hm using fun n ↦ hmid (x n) (y n)
  have hc : CauchySeq (fun n ↦ f (mid n)) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.mp hx.cauchySeq ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hy.cauchySeq ε hε
    refine ⟨max M N, fun i hi j hj ↦ ?_⟩
    have h₁ := hM i ((le_max_left M N).trans hi) j ((le_max_left M N).trans hj)
    have h₂ := hN i ((le_max_right M N).trans hi) j ((le_max_right M N).trans hj)
    have h := hT (by norm_num) (by norm_num) (hm i) (hm j)
    simp only [hf.dist_eq] at h₁ h₂ ⊢
    linarith only [h₁, h₂, h]
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨z, ?_, ?_⟩
  · apply tendsto_nhds_unique (hx.dist hz)
    exact ((hx.dist hy).const_mul (1 / 2 : ℝ)).congr fun n ↦ by
      simpa only [hf.dist_eq] using (hm n).1.symm
  · apply tendsto_nhds_unique (hz.dist hy)
    exact ((hx.dist hy).const_mul (1 - 1 / 2 : ℝ)).congr fun n ↦ by
      simpa only [hf.dist_eq] using (hm n).2.symm

end WireGeometry

end VPVNP
end Computability
end OAI

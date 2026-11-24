import OAI.Computability.VPVNP.SpectralTangentRay
import Mathlib.Topology.Order.Monotone

/-! # The radial slope and its equality case

The proof of Lemma 4.1 of *VP and VNP differ over every field* compares
the endpoint distance with the right limit of the equal-parameter ratios.
Equality forces the original segments to have the same equal-parameter
distances as their tangent rays.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireGeometry

open Set Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {o x y : X}

theorem radialSlope_nonneg (a : RadialSegment o x) (b : RadialSegment o y) : 0 ≤ radialSlope a b := by
  refine le_csInf ((nonempty_Ioc.mpr (zero_lt_one : (0 : ℝ) < 1)).image _) ?_
  rintro _ ⟨t, ht, rfl⟩
  exact div_nonneg dist_nonneg ht.1.le

/-- The radial ratios converge from the right at zero to their infimum. -/
theorem radialRatio_tendsto (hT : FractionTransport X)
    (a : RadialSegment o x) (b : RadialSegment o y) :
    Tendsto (fun t ↦ dist (a.path t) (b.path t) / t) (𝓝[>] (0 : ℝ)) (𝓝 (radialSlope a b)) := by
  refine tendsto_order.mpr ⟨fun l hl => ?_, fun u hu => ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    exact hl.trans_le (radialSlope_le_ratio a b ⟨ht.1, ht.2.le⟩)
  · obtain ⟨_, ⟨t, ht, rfl⟩, htu⟩ := exists_lt_of_csInf_lt
      ((nonempty_Ioc.mpr (zero_lt_one : (0 : ℝ) < 1)).image _) hu
    filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
    exact (radial_ratio_mono hT a b ⟨hs.1, hs.2.le.trans ht.2⟩ ht hs.2.le).trans_lt htu

/-- The distance between endpoints attains the radial slope exactly when the
equal-parameter distance between the two original segments grows linearly. -/
theorem radialSlope_eq_endpoint (hT : FractionTransport X)
    (a : RadialSegment o x) (b : RadialSegment o y) :
    radialSlope a b = dist x y ↔
      ∀ t ∈ Icc (0 : ℝ) 1, dist (a.path t) (b.path t) = radialSlope a b * t := by
  constructor
  · intro heq t ht
    rcases eq_or_lt_of_le ht.1 with rfl | hpos
    · simp [a.start, b.start]
    · apply (div_eq_iff hpos.ne').mp
      apply le_antisymm _ (radialSlope_le_ratio a b ⟨hpos, ht.2⟩)
      have h := radial_ratio_mono hT a b ⟨hpos, ht.2⟩ (show (1 : ℝ) ∈ Ioc 0 1 from ⟨zero_lt_one, le_rfl⟩) ht.2
      simpa [heq, a.finish, b.finish] using h
  · intro heq
    simpa [a.finish, b.finish] using (heq 1 ⟨zero_le_one, le_rfl⟩).symm

end WireGeometry

end VPVNP
end Computability
end OAI

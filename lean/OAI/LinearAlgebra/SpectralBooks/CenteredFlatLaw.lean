import OAI.LinearAlgebra.SpectralBooks.EuclideanPrice
import OAI.LinearAlgebra.SpectralBooks.FlatPatch
import OAI.LinearAlgebra.SpectralBooks.MinkowskiDensity
import OAI.LinearAlgebra.SpectralBooks.PatchContinuity
import OAI.LinearAlgebra.SpectralBooks.PatchHull
import OAI.LinearAlgebra.SpectralBooks.TangentProperties

/-! # Diagonal prices in a convex Euclidean patch

Rescale the finite price inequalities directly at an interior point. Their
limits have the homogeneous flat law, and the normal-cone estimates integrate
these local price identities along dilations of the configuration.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open Filter Set
open scoped Topology Classical

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {C : Set E} {δ : Finset E → ℝ}

/-- At every interior point the tangent price exists and is normalized mean width. -/
theorem DiagonalPriceLawsOn.hasTangentMeanWidth (H : DiagonalPriceLawsOn C δ) {y : E}
    (hy : y ∈ interior C) : HasTangentMeanWidth δ y := by
  obtain ⟨D, hD⟩ := exists_tangentPriceAt H.jointlyConvex hy (H.singleton (interior_subset hy))
    H.nonneg
  have hpair (a b : E) : D {a,b} = dist a b := by
    have hAB : ({a,b} : Finset E).Nonempty := Finset.insert_nonempty _ _
    apply tendsto_nhds_unique (hD _ hAB)
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin, eventually_patch_image_subset hy {a,b}]
      with h (hh : 0 < h) hsub
    have hmem (x : E) (hx : x ∈ ({a,b} : Finset E)) := hsub (Finset.mem_image_of_mem _ hx)
    simp only [Finset.image_insert, Finset.image_singleton, H.wire _ (hmem a (by simp)) _ (hmem b (by simp)),
      dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hh]
    field_simp
  have htriangle (a b c : E) : D {a,b,c} ≤ (dist a b + dist b c + dist c a) / 2 := by
    have hABC : ({a,b,c} : Finset E).Nonempty := Finset.insert_nonempty _ _
    apply le_of_tendsto (hD _ hABC)
    filter_upwards [self_mem_nhdsWithin, eventually_patch_image_subset hy {a,b,c}]
      with h (hh : 0 < h) hsub
    have hmem (x : E) (hx : x ∈ ({a,b,c} : Finset E)) := hsub (Finset.mem_image_of_mem _ hx)
    have htri := H.triangle_le _ (hmem a (by simp)) _ (hmem b (by simp)) _ (hmem c (by simp))
    simp only [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hh] at htri
    simp only [Finset.image_insert, Finset.image_singleton, div_le_iff₀ hh]
    linarith only [htri]
  intro S hS
  have hflat := homogeneousFlatLaw_of_triangle_le D (hD.jointlyConvex hy H.jointlyConvex)
    (fun _ _ hne hst ↦ hD.monotone hy (fun _ _ _ h _ ↦ H.monotone h) hne hst)
    (hD.intersectingSubmodular hy (fun _ _ _ _ hab ↦ H.submodular hab)) hD.homogeneous hpair htriangle S hS
  rw [← hflat]
  exact hD S hS

/-- The flat diagonal law with the origin chosen in the relative interior and
adjoined to the finite set of sites. -/
theorem centeredFlatDiagonalLaw (H : DiagonalPriceLawsOn C δ) (hC : Convex ℝ C)
    (h0int : (0 : E) ∈ interior C) (S : Finset E) (hS0 : 0 ∈ S) (hSC : (S : Set E) ⊆ C) :
    δ S = meanWidth S ⟨0,hS0⟩ := by
  have hS : S.Nonempty := ⟨0, hS0⟩
  have hl (t : ℝ) (ht : t ∈ Icc 0 1) (x : E) (hx : x ∈ S) : t • x ∈ C := by
    simpa using hC (interior_subset h0int) (hSC hx)
      (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  apply flatDiagonalLaw_of_tangentMeanWidth δ H.monotone H.submodular hS0
    (H.singleton (interior_subset h0int))
  · intro t ht T hT
    refine H.jointlyConvex.price_union_of_subset_convexHull hC (fun _ _ _ h _ ↦ H.monotone h)
      _ T (hS.image _) ?_ hT
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    exact hl t (Ioo_subset_Icc_self ht) x hx
  · simpa using H.jointlyConvex.convexOn_dilation S hS 0 (convex_Icc (0 : ℝ) 1)
      (fun t ht x hx ↦ by simpa using hl t ht x hx)
  · exact continuousOn_price_image δ (fun _ _ _ h ↦ H.monotone h) H.submodular
      (fun _ hx _ hy ↦ H.pair hx hy) S hS (fun x t ↦ t • x)
      (fun x hx t ht ↦ hl t ht x hx) (by fun_prop)
  · intro t ht v hv
    apply H.hasTangentMeanWidth
    simpa using hC.combo_interior_self_mem_interior h0int (hSC hv)
      (sub_pos.mpr ht.2) ht.1 (sub_add_cancel 1 t)

end

end

end SpectralBooks
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.SpectralBooks.Book.BookTangentLimit

/-! # A spectral plane from a nonhorizontal tangent direction

The convex hull of a line and a positive-height apex contains the entire
open strip strictly between them. Blowing up at half the height gives
spectral prices on the whole Euclidean plane over the same field.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open Filter Topology Set WithLp

/-- The hull of a horizontal flat and a positive-height apex contains
the entire strip of intermediate heights. -/
theorem mem_flatApexHull_of_height {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) {H : ℝ} (hH : 0 < H) (z : Book.Lift E) (hz : z.snd ∈ Ioo 0 H) :
    z ∈ flatApexHull a H := by
  let t := z.snd / H
  have ht₀ : 0 ≤ t := div_nonneg hz.1.le hH.le
  have ht₁ : t < 1 := (div_lt_one hH).2 hz.2
  let v := (1-t)⁻¹ • (z.fst - t • a)
  have hm := (convex_convexHull ℝ _)
    (flatApexHull_base_mem a H v) (flatApexHull_apex_mem a H)
    (sub_nonneg.mpr ht₁.le) ht₀ (sub_add_cancel 1 t)
  have he : (1-t) • toLp 2 (v, (0 : ℝ)) + t • toLp 2 (a, H) = z := by
    apply ofLp_injective
    apply Prod.ext
    · change (1-t) • ((1-t)⁻¹ • (z.fst - t • a)) + t • a = z.fst
      rw [smul_smul, mul_inv_cancel₀ (sub_pos.mpr ht₁).ne', one_smul, sub_add_cancel]
    · change (1-t) * 0 + (z.snd / H) * H = z.snd
      simp [hH.ne']
  rwa [he] at hm

/-- Prices on a neighborhood of a point of a Euclidean space induce prices
on the entire space by integer magnification about that point. -/
def SpectralPlacementPrices.ofNeighborhood {E K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Field K] {U : Set E} {o : E} (hU : U ∈ 𝓝 o) (P : SpectralPlacementPrices K U) :
    SpectralPlacementPrices K E := by
  classical
  let φ (x : E) : U := if h : x ∈ U then ⟨x,h⟩ else ⟨o, mem_of_mem_nhds hU⟩
  have hφ : ∀ x ∈ U, ∀ y ∈ U, dist (φ x) (φ y) = dist x y := by
    intro x hx y hy
    simp only [φ, dite_eq_left hx, dite_eq_left hy, Subtype.dist_eq]
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  let s (n : ℕ) : ℝ := 1 / (n+1)
  have hs (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  exact (Book.blowupSpectralPrices ω hs (φ o) P).pullback (Book.tangentFlat ω hs hφ hU)
    (Book.isometry_tangentFlat ω hs hφ hU (Ultrafilter.of_le _)
      tendsto_one_div_add_atTop_nhds_zero_nat)

/-- A nonhorizontal apex over a spectral line yields the same field's
spectral prices on the full two-dimensional Euclidean space. -/
def SpectralPlacementPrices.planeOfFlatApexHull {K : Type*} [Field K] {a H : ℝ} (hH : 0 < H)
    (P : SpectralPlacementPrices K (flatApexHull a H)) :
    SpectralPlacementPrices K (EuclideanSpace ℝ (Fin 2)) := by
  let c : Book.Lift ℝ := toLp 2 (a, H/2)
  have hc : c.snd ∈ Ioo (0 : ℝ) H := ⟨by change 0 < H/2; linarith, by change H/2 < H; linarith⟩
  have hn : flatApexHull a H ∈ 𝓝 c :=
    mem_of_superset ((show Continuous (fun x : Book.Lift ℝ ↦ x.snd) from WithLp.continuous_snd ..).continuousAt (Ioo_mem_nhds hc.1 hc.2))
      (fun z hz ↦ mem_flatApexHull_of_height a hH z hz)
  let f (x : EuclideanSpace ℝ (Fin 2)) : Book.Lift ℝ := toLp 2 (x 0, x 1)
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro x y
    rw [WithLp.prod_dist_eq_of_L2, EuclideanSpace.dist_eq, Fin.sum_univ_two]
    rfl
  exact (P.ofNeighborhood hn).pullback f hf

end

end

end SpectralBooks
end LinearAlgebra
end OAI

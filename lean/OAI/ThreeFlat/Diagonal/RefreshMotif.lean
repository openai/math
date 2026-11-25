import OAI.ThreeFlat.Diagonal.RefreshDense
import OAI.ThreeFlat.Diagonal.PortMotifGrid
import OAI.ThreeFlat.PortExtension
import OAI.LinearAlgebra.SpectralBooks.FinitePriceSpace

namespace OAI
/-! # The refresh motif on a finite set of ports

There are two dense sets of ties, one for the incoming and one for the
outgoing bundles. A degree-`h` Poincaré expander supplies the internal
wires. Normalizing each dense tie to unit mass and each supply arc to
`m / d₀` makes the distortion independent of the temporary port count `m`.
-/

namespace ThreeFlat.Diagonal.RefreshMotif

open LinearAlgebra.SpectralBooks SiteTensor HyperbolicObstruction Expander Computability.VPVNP.MotifGrid

variable {K : Type*} [Field K] {m h d₀ : ℕ} [Nonempty (Fin m)]

def sparseGraph (c : Fin m → Fin m → ℕ) : PortGraph (Fin m) (Arc c) := ⟨arcStart, arcEnd⟩

/-- The position of every finite tensor-price point in a complete spectral
CAT(0) realization preserves the expander's squared-distance estimate. -/
theorem wire_poincare (c : Fin m → Fin m → ℕ) (hh : 0 < h) {γ : ℝ}
    (hb : ∀ (Y : Type) [MetricSpace Y] [CompleteSpace Y], SpectralPlacementPrices K Y →
       CATZero Y → Bound (transition c h) Y γ)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin m) K → _ → Prop)) :
    (∑ i, ∑ j, rawWireDistance φ 1 i j ^ 2) ≤
      (γ * m / h) * ∑ e : Arc c, rawWireDistance φ 1 (arcStart e) (arcEnd e) ^ 2 := by
  obtain ⟨X, mx, P, x, _, hx, _⟩ := exists_metric_price_realization φ 1 zero_le_one
  let := mx
  obtain ⟨Y, my, Q, ⟨f⟩, hc, hcat⟩ := P.exists_complete_catZero_extension
  let := my
  let := hc
  have r := (hb Y Q hcat).sum_sq_le_arcs hh (fun i => f.map (x i))
  simpa only [f.isometry.dist_eq, hx, Fintype.card_fin] using r

/-- Quadratic comparison for the two port graphs in the finite-grid
conversion. The multiplier has no dependence on the size of the port set. -/
theorem energy_bound (c : Fin m → Fin m → ℕ) (hh : 0 < h) (hd : 0 < d₀) {γ : ℝ}
    (hb : ∀ (Y : Type) [MetricSpace Y] [CompleteSpace Y], SpectralPlacementPrices K Y →
       CATZero Y → Bound (transition c h) Y γ)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin m) K → _ → Prop)) :
    distanceEnergy (fun _ => (1 : ℝ)) (fun i => rawWireDistance φ 1 ((denseGraph m).tail i) ((denseGraph m).head i)) ≤
      (2 * γ * d₀ / h) * distanceEnergy (fun _ => (m : ℝ) / d₀)
        (fun i => rawWireDistance φ 1 ((sparseGraph c).tail i) ((sparseGraph c).head i)) := by
  have bound := wire_poincare c hh hb φ
  simp only [distanceEnergy, denseGraph, sparseGraph, Fintype.sum_prod_type,
    Fintype.sum_bool, one_mul, ← Finset.mul_sum]
  have hd' : (d₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hh' : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hh.ne'
  rw [← two_mul]
  calc
    _ ≤ 2 * ((γ * m / h) * ∑ e : Arc c, rawWireDistance φ 1 (arcStart e) (arcEnd e) ^ 2) :=
      mul_le_mul_of_nonneg_left bound (by norm_num)
    _ = _ := by field_simp


end ThreeFlat.Diagonal.RefreshMotif

end OAI

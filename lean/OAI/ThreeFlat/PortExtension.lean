import OAI.LinearAlgebra.SpectralBooks.Theorem
import OAI.ThreeFlat.PortArcBound

namespace OAI
/-! # Pricing port traffic in spectral metric spaces -/

namespace ThreeFlat.Expander
open HyperbolicObstruction LinearAlgebra.SpectralBooks Finset
universe u

/-- A finite traffic pattern in any spectral metric space has the same
first-moment bound, by embedding it into its complete CAT(0) extension. -/
theorem port_demand_bound_of_spectral_extension {F V : Type*} {X : Type u} [Field F]
    [Fintype V] [Nonempty V] [MetricSpace X] (P : SpectralPlacementPrices F X)
    {c : V → V → ℕ} {h : ℕ} (hh : 0 < h) {γ W : ℝ} (hγ : 0 ≤ γ) (hW : 0 ≤ W)
    (hscalar : Bound (transition c h) ℝ γ)
    (hb : ∀ (Y : Type u) [MetricSpace Y] [CompleteSpace Y], SpectralPlacementPrices F Y →
      CATZero Y → Bound (transition c h) Y γ)
    (x : V → X) (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hout : ∀ i, ∑ j, w i j ≤ W) (hin : ∀ j, ∑ i, w i j ≤ W) :
    (∑ i, ∑ j, w i j * dist (x i) (x j)) ≤
      (40 * W * γ / h) * ∑ e : Arc c, dist (x (arcStart e)) (x (arcEnd e)) := by
  obtain ⟨Y, m, Q, ⟨f⟩, hc, hcat⟩ := P.exists_complete_catZero_extension
  let _ := m
  let _ := hc
  simpa only [f.isometry.dist_eq] using
    port_demand_bound hcat hh hγ hW hscalar (hb Y Q hcat) (fun i => f.map (x i)) w hw hout hin

end ThreeFlat.Expander

end OAI

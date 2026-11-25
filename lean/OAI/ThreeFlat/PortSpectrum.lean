import OAI.ThreeFlat.PortArcBound
import OAI.LinearAlgebra.SpectralBooks.FinitePlaneCriterion

namespace OAI
/-! # Spectral prices and connectedness of a cloud's supply graph -/

namespace ThreeFlat.RouteUnits

open Expander LinearAlgebra.SpectralBooks SiteTensor
open scoped BigOperators

variable {V : Type} [Fintype V] [Nonempty V] {h : ℕ} {γ : ℝ} {c : V → V → ℕ}

/-- A scalar spectral gap forces every Boolean label constant on the
individual arcs to be constant across the cloud. -/
theorem port_connected (hh : 0 < h) (scalar : Bound (transition c h) ℝ γ) (root : V)
    (f : V → Bool) (same : ∀ e : Arc c, f (arcStart e) = f (arcEnd e)) :
    ∀ v, f v = f root := by
  classical
  let x (i : V) : ℝ := if f i then 1 else 0
  have hx (e : Arc c) : x (arcStart e) = x (arcEnd e) := by simp only [x, same e]
  have gap := scalar.sum_sq_le_arcs hh x
  simp only [hx, dist_self, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero] at gap
  intro v
  have bnd : dist (x v) (x root)^2 ≤ ∑ i, ∑ j, dist (x i) (x j)^2 := by
    exact (Finset.single_le_sum (fun j _ => sq_nonneg (dist (x v) (x j))) (Finset.mem_univ root)).trans
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (dist (x i) (x j))))
        (Finset.mem_univ v))
  have eqn : x v = x root := dist_eq_zero.mp (by nlinarith [bnd.trans gap])
  cases h₁ : f v <;> cases h₂ : f root <;> simp_all [x]

/-- Apply the same normalized spectral point to both the demand and supply
wire lists, including parallel arcs and loops. -/
theorem raw_port_demand_bound {F : Type*} [Field F] (hh : 0 < h) (hγ : 0 ≤ γ)
    (scalar : Bound (transition c h) ℝ γ)
    (spectral : ∀ (X : Type) [MetricSpace X] [CompleteSpace X], SpectralPlacementPrices F X →
      HyperbolicObstruction.CATZero X → Bound (transition c h) X γ)
    (w : V → V → ℕ) (B : ℕ) (out : ∀ i, ∑ j, w i j ≤ B) (inc : ∀ j, ∑ i, w i j ≤ B)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} V F → _ → Prop)) :
    (∑ e : V × V, (w e.1 e.2 : ℝ) * rawWireDistance φ 1 e.1 e.2) ≤
      (40 * B * γ / h) * ∑ e : Arc c, rawWireDistance φ 1 (arcStart e) (arcEnd e) := by
  obtain ⟨X, met, P, x, complete, geo, hd, _⟩ :=
    SpectralPlacementPrices.realize_finite_point_geodesic φ 1 zero_le_one
  let := met
  let := complete
  have cat := P.catZero geo
  have bound := port_demand_bound cat hh hγ (show 0 ≤ (B:ℝ) by positivity) scalar
    (spectral X P cat) x (fun i j => (w i j : ℝ)) (fun _ _ => by positivity)
    (fun i => by exact_mod_cast out i) (fun j => by exact_mod_cast inc j)
  simpa only [Fintype.sum_prod_type, hd] using bound

end ThreeFlat.RouteUnits

end OAI

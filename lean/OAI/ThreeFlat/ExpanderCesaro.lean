import OAI.ThreeFlat.ExpanderWalk
import OAI.ThreeFlat.ExpanderWalkCompare
import OAI.ThreeFlat.ExpanderWalkSum

namespace OAI
/-! # The quadratic Poincaré bound of a Cesàro-averaged lazy walk -/

namespace ThreeFlat.Expander

open Finset Matrix Computability.VPVNP.SpectralGeometry

variable {V X : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [PseudoMetricSpace X] [CompleteSpace X]

/-- At even time `2*k`, barycentric smoothing amplifies the Poincaré bound
of a stationary lazy walk on every complete CAT(0) target. -/
theorem bound_cesaro_lazy (hX : HasCATZeroSegments X) {G : Matrix V V ℝ}
    (hrow : G ∈ rowStochastic ℝ V) (hcol : G ∈ colStochastic ℝ V)
    {γ : ℝ} (hγ : 0 ≤ γ) (hbound : Bound G X γ) {k : ℕ} (hk : 0 < k) :
    Bound (cesaro (lazyStep G) (2*k)) X (48 * (1 + γ / (2 * (k : ℝ)))) := by
  intro x
  let : Nonempty X := ⟨x (Classical.choice ‹Nonempty V›)⟩
  let A := lazyStep G
  have hr : A ∈ rowStochastic ℝ V := lazyStep_row hrow
  have hc : A ∈ colStochastic ℝ V := lazyStep_col hcol
  let y := walkPlacement hX hr x
  let D := fun g => avg (fun i => dist (x i) (y g i)^2)
  let E := fun g => avg (walkError hX hr x g)
  have hE (g : ℕ) : 0 ≤ E g :=
    avg_nonneg fun i => sum_nonneg fun j _ => mul_nonneg (hr.1 i j) (sq_nonneg _)
  have hD (g : ℕ) : 0 ≤ D g := avg_nonneg fun _ => sq_nonneg _
  have hW (g : ℕ) : variance x ≤ 6*D g + 12*γ*E g := by
    have hstep : energy G (y g) ≤ 4 * E g :=
      energy_le_lazy_crossEnergy G hrow (y g) (y (g+1))
    have hy := (hbound (y g)).trans (mul_le_mul_of_nonneg_left hstep hγ)
    have hx : variance x ≤ 3 * (2 * D g + variance (y g)) :=
      variance_le_via_placement x (y g)
    linarith
  have h := walk_scalar_bound hk hγ hE hD
    (walk_distance_add_errors_le_energy hX hr hc x) hW
  simpa only [energy_cesaro, Nat.cast_mul, Nat.cast_ofNat] using h

end ThreeFlat.Expander

end OAI

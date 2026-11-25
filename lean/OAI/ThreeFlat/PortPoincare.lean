import OAI.ThreeFlat.PortCenter
import OAI.ThreeFlat.PortCoarea
import OAI.ThreeFlat.PortClip
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI
/-! # A first-moment Poincaré inequality for port graphs

A quadratic Poincaré inequality on a CAT(0) space and on the real line
bounds the sum of all pair distances by the sum of edge lengths.
The edge type may enumerate a multigraph with repetitions.
-/

namespace ThreeFlat

open Finset
open scoped BigOperators

private theorem pair_cauchy {V : Type*} [Fintype V] (d : V → V → ℝ) :
    (∑ i, ∑ j, d i j)^2 ≤ (Fintype.card V : ℝ)^2 * ∑ i, ∑ j, (d i j)^2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (V × V)))
    (f := fun ij => d ij.1 ij.2)
  simpa [Fintype.sum_prod_type, Fintype.card_prod, sq] using h

/-- Unnormalized Poincaré constants for squared distances imply the corresponding
sum inequality for distances, with a universal factor at most twenty. -/
theorem port_distance_poincare {V E X : Type*} [Fintype V] [Nonempty V] [Fintype E]
    [MetricSpace X] (hX : HyperbolicObstruction.CATZero X) (l r : E → V) (C : ℝ)
    (hC : 0 ≤ C)
    (hscalar : ∀ f : V → ℝ, (∑ i, ∑ j, (f i - f j)^2) ≤
      C * ∑ e, (f (l e) - f (r e))^2)
    (hmetric : ∀ f : V → X, (∑ i, ∑ j, (dist (f i) (f j))^2) ≤
      C * ∑ e, (dist (f (l e)) (f (r e)))^2) (f : V → X) :
    (∑ i, ∑ j, dist (f i) (f j)) ≤ (20*C) * ∑ e, dist (f (l e)) (f (r e)) := by
  classical
  let m : ℝ := Fintype.card V
  have hm : 0 < m := Nat.cast_pos.mpr Fintype.card_pos
  let A := ∑ i, ∑ j, dist (f i) (f j)
  let B := ∑ e, dist (f (l e)) (f (r e))
  let R := 4 * (A / m^2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨o, _, hsmall⟩ := exists_port_center f
  obtain ⟨p, ph, pr, plip⟩ := exists_port_clip hX (f o) hR
  let g := p ∘ f
  let rad (i : V) := max (dist (f i) (f o) - R) 0
  have rad_pos (i) : 0 ≤ rad i := le_max_right _ _
  have rad_small : (univ.filter fun i => 0 < rad i).card ≤ Fintype.card V / 2 := by
    dsimp only [rad]
    simp only [lt_max_iff, lt_self_iff_false, or_false, sub_pos]
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr (by simpa [Nat.mul_comm, R, A, m] using hsmall)
  have hsum := sum_radius_le_edge_variation l r rad rad_pos (C/m) (Fintype.card V / 2)
    rad_small (fun s hs => by
      have hcut := cutEdgeCount_of_scalar_poincare l r s (by omega) hscalar
      calc
        (s.card : ℝ) ≤ C * cutEdgeCount l r s / m := (le_div_iff₀ hm).mpr hcut
        _ = C / m * cutEdgeCount l r s := by ring)
  have var (i j : V) : |rad i - rad j| ≤ dist (f i) (f j) := by
    have h := abs_dist_sub_le (f i) (f j) (f o)
    rw [abs_le] at h ⊢
    dsimp only [rad]
    have hd : 0 ≤ dist (f i) (f j) := dist_nonneg
    constructor <;> grind
  have rem : m * ∑ i, rad i ≤ C*B := by
    have h' := hsum.trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun e _ => var (l e) (r e))) (div_nonneg hC hm.le))
    calc
      m * ∑ i, rad i ≤ m * (C / m * B) := mul_le_mul_of_nonneg_left h' hm.le
      _ = C * B := by field_simp
  let H := ∑ i, ∑ j, dist (g i) (g j)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have pair_dist (i j : V) : dist (f i) (f j) ≤ rad i + dist (g i) (g j) + rad j := by
    have h₁ := dist_triangle (f i) (g i) (g j)
    have h₂ := dist_triangle (f i) (g j) (f j)
    rw [show dist (f i) (g i) = rad i from pr (f i)] at h₁
    rw [dist_comm (g j) (f j), show dist (f j) (g j) = rad j from pr (f j)] at h₂
    linarith
  have tri : A ≤ H + 2*(C*B) := by
    calc
      A ≤ ∑ i, ∑ j, (rad i + dist (g i) (g j) + rad j) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => pair_dist i j
      _ = H + 2 * (m * ∑ i, rad i) := by
        simp [H, m, Finset.sum_add_distrib, nsmul_eq_mul, ← Finset.mul_sum]
        ring
      _ ≤ H + 2*(C*B) := by linarith
  have edge_range (i j : V) : dist (g i) (g j) ≤ 2*R := by
    have h := dist_triangle_right (g i) (g j) (f o)
    have hi : dist (g i) (f o) ≤ R := ph (f i)
    have hj : dist (g j) (f o) ≤ R := ph (f j)
    linarith
  have edge_sq (e : E) :
      dist (g (l e)) (g (r e))^2 ≤ (4*R)*dist (f (l e)) (f (r e)) := by
    calc
      _ ≤ (2*R) * (2*dist (f (l e)) (f (r e))) := by
        rw [sq]
        exact mul_le_mul (edge_range _ _) (plip _ _) dist_nonneg (by positivity)
      _ = _ := by ring
  have hsq : H^2 ≤ 16 * A * (C*B) := by
    calc
      H^2 ≤ m^2 * (∑ i, ∑ j, dist (g i) (g j)^2) :=
        pair_cauchy (fun i j => dist (g i) (g j))
      _ ≤ m^2 * (C * ∑ e, dist (g (l e)) (g (r e))^2) :=
        mul_le_mul_of_nonneg_left (hmetric g) (sq_nonneg _)
      _ ≤ m^2 * (C * ∑ e, (4*R)*dist (f (l e)) (f (r e))) := by
        gcongr
        exact edge_sq _
      _ = 16 * A * (C*B) := by
        rw [← Finset.mul_sum]
        dsimp only [R, B]
        field_simp
        ring
  have bound : H ≤ A/2 + 8*(C*B) := by
    have hright : 0 ≤ A/2 + 8*(C*B) := by positivity
    have hpow : H^2 ≤ (A/2 + 8*(C*B))^2 := by
      nlinarith [sq_nonneg (A/2 - 8*(C*B))]
    exact (sq_le_sq₀ hH hright).mp hpow
  change A ≤ 20*C*B
  linarith

/-- The ports' graph edges pay for any nonnegative demand table with
uniformly bounded row and column loads. -/
theorem port_demand_poincare {V E X : Type*} [Fintype V] [Nonempty V] [Fintype E]
    [MetricSpace X] (hX : HyperbolicObstruction.CATZero X) (l r : E → V) {C W : ℝ}
    (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hscalar : ∀ f : V → ℝ, (∑ i, ∑ j, (f i - f j)^2) ≤
      C * ∑ e, (f (l e) - f (r e))^2)
    (hmetric : ∀ f : V → X, (∑ i, ∑ j, (dist (f i) (f j))^2) ≤
      C * ∑ e, (dist (f (l e)) (f (r e)))^2) (f : V → X)
    (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j) (hout : ∀ i, ∑ j, w i j ≤ W)
    (hin : ∀ j, ∑ i, w i j ≤ W) :
    ∑ i, ∑ j, w i j * dist (f i) (f j) ≤
      (40 * W * C / Fintype.card V) * ∑ e, dist (f (l e)) (f (r e)) := by
  obtain ⟨o, ho, _⟩ := exists_port_center f
  have hm : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have h := port_distance_poincare hX l r C hC hscalar hmetric f
  calc
    _ ≤ 2*W * ∑ i, dist (f i) (f o) := port_demand_cost_le f o w W hw hout hin
    _ ≤ 2*W * (((20*C) * ∑ e, dist (f (l e)) (f (r e))) / Fintype.card V) :=
      mul_le_mul_of_nonneg_left (ho.trans (div_le_div_of_nonneg_right h hm.le)) (by positivity)
    _ = _ := by ring

end ThreeFlat

end OAI

import OAI.ThreeFlat.ExpanderBasic
import OAI.ThreeFlat.PortPoincare

namespace OAI
/-! # Port-price bounds for the arcs of a regular multigraph -/

namespace ThreeFlat.Expander

open Finset

/-- Every copy of an oriented edge is a separate arc, including each loop. -/
abbrev Arc {V : Type*} (c : V → V → ℕ) := Σ ij : V × V, Fin (c ij.1 ij.2)

def arcStart {V : Type*} {c : V → V → ℕ} (e : Arc c) : V := e.1.1

def arcEnd {V : Type*} {c : V → V → ℕ} (e : Arc c) : V := e.1.2

variable {V X : Type*} [Fintype V]

theorem sum_arcs (c : V → V → ℕ) (f : V → V → ℝ) :
    (∑ e : Arc c, f (arcStart e) (arcEnd e)) = ∑ i, ∑ j, (c i j : ℝ) * f i j := by
  rw [Fintype.sum_sigma, Fintype.sum_prod_type]
  simp [arcStart, arcEnd, nsmul_eq_mul]

theorem energy_transition_arc_sum [PseudoMetricSpace X] (c : V → V → ℕ) (h : ℕ)
    (x : V → X) : energy (transition c h) x =
    ((∑ e : Arc c, dist (x (arcStart e)) (x (arcEnd e))^2) / h) / Fintype.card V := by
  rw [sum_arcs c (fun i j => dist (x i) (x j)^2)]
  simp only [energy, avg, transition, div_mul_eq_mul_div, ← sum_div]

/-- Undo both uniform vertex averages in a Poincaré inequality. The raw sum
retains one factor of the number of vertices divided by the graph degree. -/
theorem Bound.sum_sq_le_arcs [Nonempty V] [PseudoMetricSpace X] {c : V → V → ℕ} {h : ℕ}
    {γ : ℝ} (hb : Bound (transition c h) X γ) (hh : 0 < h) (x : V → X) :
    (∑ i, ∑ j, dist (x i) (x j)^2) ≤
    (γ * Fintype.card V / h) * ∑ e : Arc c, dist (x (arcStart e)) (x (arcEnd e))^2 := by
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have hd : (0 : ℝ) < h := by exact_mod_cast hh
  have bound := hb x
  simp only [variance, avg, ← sum_div, energy_transition_arc_sum] at bound
  exact ((div_le_iff₀ hn).mp ((div_le_iff₀ hn).mp bound)).trans_eq
    (by field_simp)

/-- Every nonnegative traffic table of row and column load at most `W` costs
at most `40*W*γ/h` times the sum of the placed arc lengths. -/
theorem port_demand_bound [Nonempty V] [MetricSpace X] (hX : HyperbolicObstruction.CATZero X)
    {c : V → V → ℕ} {h : ℕ} (hh : 0 < h) {γ W : ℝ} (hγ : 0 ≤ γ) (hW : 0 ≤ W)
    (hscalar : Bound (transition c h) ℝ γ) (hmetric : Bound (transition c h) X γ)
    (x : V → X) (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j) (hout : ∀ i, ∑ j, w i j ≤ W)
    (hin : ∀ j, ∑ i, w i j ≤ W) :
    (∑ i, ∑ j, w i j * dist (x i) (x j)) ≤
      (40 * W * γ / h) * ∑ e : Arc c, dist (x (arcStart e)) (x (arcEnd e)) := by
  have scalar (f : V → ℝ) := hscalar.sum_sq_le_arcs hh f
  simp only [Real.dist_eq, sq_abs] at scalar
  have result := port_demand_poincare hX (arcStart (c := c)) (arcEnd (c := c))
    (C := γ * Fintype.card V / h) (by positivity) hW scalar
    (hmetric.sum_sq_le_arcs hh) x w hw hout hin
  have hn : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hd : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hh.ne'
  calc
    _ ≤ _ := result
    _ = _ := by field_simp

end ThreeFlat.Expander

end OAI

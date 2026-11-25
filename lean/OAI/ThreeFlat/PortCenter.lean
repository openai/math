import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

namespace OAI
/-! # Choosing a center for the port graph

A vertex minimizing the sum of distances to the configuration has mean
radius at most the mean pair distance. At most half of the configuration
lies beyond four times the latter distance.
-/

namespace ThreeFlat

open scoped BigOperators Classical

theorem exists_port_center {V X : Type*} [Fintype V] [Nonempty V] [PseudoMetricSpace X]
    (f : V → X) :
    ∃ o : V,
      (∑ i, dist (f i) (f o)) ≤ (∑ i, ∑ j, dist (f i) (f j)) / (Fintype.card V : ℝ) ∧
      2 * (Finset.univ.filter fun i =>
        4 * ((∑ i, ∑ j, dist (f i) (f j)) / (Fintype.card V : ℝ) ^ 2) <
          dist (f i) (f o)).card ≤ Fintype.card V := by
  classical
  let n : ℝ := Fintype.card V
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast Fintype.card_pos (α := V)
  let A : ℝ := ∑ i, ∑ j, dist (f i) (f j)
  let L := A / n ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg
  have hL : 0 ≤ L := div_nonneg hA (sq_nonneg _)
  let R (o : V) := ∑ i, dist (f i) (f o)
  obtain ⟨o, _, hmin⟩ := Finset.univ.exists_min_image R Finset.univ_nonempty
  have hminsum : R o * n ≤ A := calc
    R o * n = ∑ _ : V, R o := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, n, mul_comm]
    _ ≤ ∑ j, R j := Finset.sum_le_sum fun j _ => hmin j (Finset.mem_univ j)
    _ = A := Finset.sum_comm
  have hradius : R o ≤ A / n := (le_div_iff₀ hn).mpr hminsum
  refine ⟨o, hradius, ?_⟩
  let S := Finset.univ.filter fun i => 4 * L < dist (f i) (f o)
  change 2 * S.card ≤ Fintype.card V
  apply le_of_not_gt
  intro hlarge
  have hcard : n ≤ 2 * (S.card : ℝ) := by
    dsimp only [n]
    exact_mod_cast hlarge.le
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hstrict : (S.card : ℝ) * (4 * L) < R o := calc
    (S.card : ℝ) * (4 * L) = ∑ _ ∈ S, 4 * L := by rw [Finset.sum_const, nsmul_eq_mul]
    _ < ∑ i ∈ S, dist (f i) (f o) :=
      Finset.sum_lt_sum_of_nonempty hS fun _ hi => (Finset.mem_filter.mp hi).2
    _ ≤ R o := Finset.sum_le_univ_sum_of_nonneg fun _ => dist_nonneg
  have heq : A / n = n * L := by
    dsimp [L]
    field_simp [hn.ne']
  have hhalf := mul_le_mul_of_nonneg_right hcard hL
  rw [heq] at hradius
  nlinarith [mul_nonneg (Nat.cast_nonneg S.card : (0 : ℝ) ≤ _) hL]

/-- The triangle inequality bounds the total price of a width table with
bounded incoming and outgoing port loads by distances from any center. -/
theorem port_demand_cost_le {V X : Type*} [Fintype V] [PseudoMetricSpace X]
    (f : V → X) (o : V) (w : V → V → ℝ) (B : ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hout : ∀ i, ∑ j, w i j ≤ B)
    (hin : ∀ j, ∑ i, w i j ≤ B) :
    ∑ i, ∑ j, w i j * dist (f i) (f j) ≤ 2 * B * ∑ i, dist (f i) (f o) := by
  let r (i : V) := dist (f i) (f o)
  have hcharge (a : V → V → ℝ) (ha : ∀ i, ∑ j, a i j ≤ B) :
      ∑ i, ∑ j, a i j * r i ≤ B * ∑ i, r i := by
    simp_rw [← Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (ha i) dist_nonneg
  calc
    _ ≤ ∑ i, ∑ j, w i j * (r i + r j) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (dist_triangle_right (f i) (f j) (f o)) (hw i j)
    _ = (∑ i, ∑ j, w i j * r i) + ∑ j, ∑ i, w i j * r j := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      exact congrArg ((∑ i, ∑ j, w i j * r i) + ·) Finset.sum_comm
    _ ≤ B * (∑ i, r i) + B * ∑ i, r i :=
      add_le_add (hcharge w hout) (hcharge (fun j i => w i j) hin)
    _ = _ := by dsimp only [r]; ring

end ThreeFlat

end OAI

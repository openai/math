import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The subdivision counts in degree regularization

In §7.2 of *VP and VNP differ over every field*, an old wire has mass
`p` and a new slot has mass `p * K * d / d'`. Thus the floor count depends
only on the degrees, the packing ratio and the supply type's relative mass.
The same degree threshold works for every position count and every term.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.SlotSubdivision

/-- Number of regularized slots for one surviving supply edge. -/
noncomputable def count (K d d' : ℕ) (q : ℝ) : ℕ := ⌊(d' : ℝ) * q / (K * d)⌋₊

/-- For the paper's rational supply masses, ordinary natural division computes
the subdivisions used in the local circuit descriptions. -/
theorem count_fraction (K d d' a b : ℕ) :
    count K d d' ((a : ℝ) / b) = d' * a / (b * K * d) := by
  rw [count, ← Nat.floor_div_eq_div (K := ℝ)]
  congr 1
  simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
  ring

variable {T : Type*}

/-- For every sufficiently large output degree, the floored counts are positive
and represent at least `1-δ` of each type's old mass. In particular the same
threshold works when output degrees are restricted to powers of two. -/
theorem eventually_represented [Finite T] (q : T → ℝ) (hq : ∀ t, 0 < q t) {K d : ℕ}
    (hK : 0 < K) (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1) :
    ∃ N : ℕ, ∀ d' ≥ N, 0 < d' ∧ ∀ (p p' : ℝ), 0 < p → p' = p * (K * d) / d' →
      ∀ t, 0 < count K d d' (q t) ∧
        (1 - δ) * p * q t ≤ (count K d d' (q t) : ℝ) * p' := by
  let := Fintype.ofFinite T
  let S : ℝ := K * d
  have hS : 0 < S := mul_pos (Nat.cast_pos.mpr hK) (Nat.cast_pos.mpr hd)
  let bound (t : T) := S / (δ * q t)
  have hbound (t : T) : 0 ≤ bound t := (div_pos hS (mul_pos hδ (hq t))).le
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ t, bound t)
  refine ⟨N, fun d' hd' ↦ ?_⟩
  have hdn : (∑ t, bound t) < (d' : ℝ) := hN.trans_le (Nat.cast_le.mpr hd')
  have hpos : 0 < (d' : ℝ) := (Finset.sum_nonneg (fun t _ ↦ hbound t)).trans_lt hdn
  refine ⟨Nat.cast_pos.mp hpos, ?_⟩
  rintro p _ hp rfl t
  have ht : bound t < (d' : ℝ) :=
    (Finset.single_le_sum (fun s _ ↦ hbound s) (Finset.mem_univ t)).trans_lt hdn
  have hscaled : S < (d' : ℝ) * (δ * q t) := (div_lt_iff₀ (mul_pos hδ (hq t))).mp ht
  let x := (d' : ℝ) * q t / S
  have hx : 0 < x := div_pos (mul_pos hpos (hq t)) hS
  have hxδ : 1 < δ * x := by
    dsimp only [x]
    rw [← mul_div_assoc]
    apply (lt_div_iff₀ hS).mpr
    simpa only [one_mul, mul_assoc, mul_left_comm] using hscaled
  have hlower : (1 - δ) * x ≤ (count K d d' (q t) : ℝ) := by
    change (1 - δ) * x ≤ (⌊x⌋₊ : ℝ)
    linarith only [Nat.lt_floor_add_one x, hxδ]
  refine ⟨Nat.cast_pos.mp ((mul_pos (sub_pos.mpr hδ') hx).trans_le hlower), ?_⟩
  calc
    (1 - δ) * p * q t = ((1 - δ) * x) * (p * S / d') := by
      dsimp only [x]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hlower (div_pos (mul_pos hp hS) hpos).le

/-- The sum of the floored subdivisions fits inside the available output degree.
Each of the four types has `d * Q` incidences at each site, and the relative
masses of one surviving group sum to `4/3`. -/
theorem degree_budget [Fintype T] (q : T → ℝ) (hq : ∀ t, 0 ≤ q t) (htotal : ∑ t, q t = 4 / 3)
    {K Q d d' : ℕ} (hK : 0 < K) (hd : 0 < d) (hQ : 4 * Q = 3 * K) :
    d * Q * ∑ t, count K d d' (q t) ≤ d' := by
  let S : ℝ := K * d
  have hS : 0 < S := mul_pos (Nat.cast_pos.mpr hK) (Nat.cast_pos.mpr hd)
  have hsum : ∑ t, (count K d d' (q t) : ℝ) ≤ (d' : ℝ) * (4 / 3) / S := calc
    _ ≤ ∑ t, (d' : ℝ) * q t / S :=
      Finset.sum_le_sum fun t _ ↦ Nat.floor_le
        (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hq t)) hS.le)
    _ = _ := by rw [← Finset.sum_div, ← Finset.mul_sum, htotal]
  have hQ' : 4 * (Q : ℝ) = 3 * (K : ℝ) := by exact_mod_cast hQ
  have h := mul_le_mul_of_nonneg_left hsum (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg Q))
  have hright : (d : ℝ) * Q * ((d' : ℝ) * (4 / 3) / S) = d' := by
    dsimp only [S]
    field_simp
    linear_combination (d' : ℝ) * hQ'
  exact_mod_cast h.trans_eq hright

end Compression.SlotSubdivision

end VPVNP
end Computability
end OAI

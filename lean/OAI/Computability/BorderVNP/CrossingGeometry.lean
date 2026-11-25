import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Displacing a junction on one side of a crossing

Section 4.4 moves a junction in the direction of the sum of its signed, orthogonal
terminals. The unchanged wires have unit length. Each bridge leaving the moved
junction, including the cut rank, now has length equal to the displacement.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open scoped RealInnerProductSpace

variable {s D : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Picking either antipode on each of a set of distinct coordinate axes gives orthonormal terminals. -/
theorem orthonormal_signed_terminals (axis : Fin s ↪ Fin D) (negative : Fin s → Bool) :
    Orthonormal ℝ fun i ↦ if negative i then -EuclideanSpace.single (axis i) (1 : ℝ)
      else EuclideanSpace.single (axis i) (1 : ℝ) := by
  have hbase : Orthonormal ℝ (fun i : Fin D ↦ EuclideanSpace.single i (1 : ℝ)) :=
    EuclideanSpace.orthonormal_single
  apply (hbase.comp axis axis.injective).orthonormal_of_forall_eq_or_eq_neg
  intro i
  cases negative i <;> simp

/-- Unit direction from the origin toward the selected terminals. -/
noncomputable def junctionDirection (u : Fin s → E) : E :=
  (Real.sqrt s)⁻¹ • ∑ i, u i

private theorem terminal_inner_sum (u : Fin s → E) (hu : Orthonormal ℝ u) (i : Fin s) :
    ⟪u i, ∑ j, u j⟫ = 1 := by
  simpa only [one_smul] using hu.inner_right_fintype (fun _ ↦ (1 : ℝ)) i

/-- Each selected terminal has the same projection onto the displacement direction. -/
theorem terminal_inner_junctionDirection (u : Fin s → E) (hu : Orthonormal ℝ u) (i : Fin s) :
    ⟪u i, junctionDirection u⟫ = (Real.sqrt s)⁻¹ := by
  rw [junctionDirection, real_inner_smul_right, terminal_inner_sum u hu, mul_one]

/-- The orthonormality of the chosen terminals normalizes their sum by the square root of their count. -/
theorem norm_junctionDirection (u : Fin s → E) (hu : Orthonormal ℝ u) (hs : 0 < s) :
    ‖junctionDirection u‖ = 1 := by
  have hsq : ‖∑ i, u i‖ ^ 2 = (s : ℝ) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp [terminal_inner_sum u hu]
  have hnorm : ‖∑ i, u i‖ = Real.sqrt s :=
    (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      (hsq.trans (Real.sq_sqrt (Nat.cast_nonneg s)).symm)
  have hroot : 0 < Real.sqrt s := Real.sqrt_pos.mpr (by exact_mod_cast hs)
  rw [junctionDirection, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hroot), hnorm,
    inv_mul_cancel₀ hroot.ne']

/-- Squared length of the wire from a terminal to the displaced junction. -/
theorem terminal_dist_displaced_sq (u : Fin s → E) (hu : Orthonormal ℝ u) (t : ℝ) (i : Fin s) :
    dist (u i) (t • junctionDirection u) ^ 2 = 1 - 2 * t / Real.sqrt s + t ^ 2 := by
  have hs : 0 < s := Fin.pos i
  rw [dist_eq_norm, norm_sub_sq_real, hu.1, real_inner_smul_right, terminal_inner_junctionDirection u hu,
    norm_smul, norm_junctionDirection u hu hs, mul_one, Real.norm_eq_abs, sq_abs]
  ring

/-- Total wire length after the selected junction moves. The first term counts the unchanged
terminal wires. The last term counts the moved bridges and the single rank index. -/
noncomputable def displacedCost (D : ℕ) (u : Fin s → E) (m b rankWidth t : ℝ) : ℝ :=
  ((2 * (D : ℝ) - s) * m) + m * ∑ i, dist (u i) (t • junctionDirection u) +
    (m * b + rankWidth) * dist (t • junctionDirection u) 0

/-- With the favorable choice of side from (4.4), moving its junction by
`0.04 / √D` saves at least `0.002 m` even after the rounded rank width is charged. -/
theorem displacedCost_le (u : Fin s → E) (hu : Orthonormal ℝ u) (hs : 0 < s)
    (hsD : s ≤ D) {m b rankWidth : ℝ} (hm : 0 ≤ m)
    (hgap : Real.sqrt D / 10 ≤ Real.sqrt s - b)
    (hrank : rankWidth ≤ 3 / 100 * m * Real.sqrt D) :
    displacedCost D u m b rankWidth (1 / (25 * Real.sqrt D)) ≤ 2 * D * m - m / 500 := by
  let t : ℝ := 1 / (25 * Real.sqrt D)
  have hD : 0 < Real.sqrt D := Real.sqrt_pos.mpr (by exact_mod_cast hs.trans_le hsD)
  have hS : 0 < Real.sqrt s := Real.sqrt_pos.mpr (by exact_mod_cast hs)
  have ht : 0 < t := by dsimp [t]; positivity
  have hunit : t * Real.sqrt D = 1 / 25 := by dsimp [t]; field_simp
  have hsqrt : (s : ℝ) / Real.sqrt s = Real.sqrt s :=
    (div_eq_iff hS.ne').mpr (by rw [← sq, Real.sq_sqrt (Nat.cast_nonneg s)])
  have hsq : t ^ 2 * (D : ℝ) = (1 / 25 : ℝ) ^ 2 := by
    rw [← Real.sq_sqrt (Nat.cast_nonneg D), ← mul_pow, hunit]
  have hlen (i : Fin s) : dist (u i) (t • junctionDirection u) ≤
      1 - t / Real.sqrt s + t ^ 2 / 2 := by
    have he := terminal_dist_displaced_sq u hu t i
    rw [mul_div_assoc] at he
    nlinarith only [he, sq_nonneg (dist (u i) (t • junctionDirection u) - 1)]
  have htotal : ∑ i, dist (u i) (t • junctionDirection u) ≤
      (s : ℝ) * (1 - t / Real.sqrt s + t ^ 2 / 2) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using Finset.sum_le_sum (fun (i : Fin s) (_ : i ∈ Finset.univ) ↦ hlen i)
  have hquad : t ^ 2 * (s : ℝ) ≤ (1 / 25 : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hsD) (sq_nonneg t)).trans_eq hsq
  have hcost : (m * b + rankWidth) * t ≤ m * (Real.sqrt s - 7 / 100 * Real.sqrt D) * t := by
    apply mul_le_mul_of_nonneg_right _ ht.le
    nlinarith only [hrank, mul_le_mul_of_nonneg_left hgap hm]
  have hmain : (s : ℝ) * (t / Real.sqrt s) = t * Real.sqrt s := by
    calc
      _ = t * ((s : ℝ) / Real.sqrt s) := by ring
      _ = _ := by rw [hsqrt]
  rw [displacedCost, show 1 / (25 * Real.sqrt D) = t from rfl, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos ht, norm_junctionDirection u hu hs, mul_one]
  nlinarith only [mul_le_mul_of_nonneg_left htotal hm, hcost,
    mul_le_mul_of_nonneg_left hquad hm, congrArg (m * ·) hmain, congrArg (m * ·) hunit]

end Crossing

end BorderVNP
end Computability
end OAI

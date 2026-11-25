import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Basic.Real.Basic

/-! # Four good columns with prescribed shifted differences -/

namespace OAI.Computability.MultitapeWeakETH

open scoped BigOperators

private theorem mean_square {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) :
    (𝔼 i, f i)^2 ≤ 𝔼 i, (f i)^2 := by
  simpa using Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f (fun _ => (1:ℝ))

private theorem fourth_moment {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) :
    (𝔼 i, f i)^4 ≤ 𝔼 i, (f i)^4 := by
  calc
    _ = ((𝔼 i, f i)^2)^2 := by ring
    _ ≤ (𝔼 i, (f i)^2)^2 := pow_le_pow_left₀ (sq_nonneg _) (mean_square f) 2
    _ ≤ 𝔼 i, ((f i)^2)^2 := mean_square _
    _ = _ := Finset.expect_congr rfl (fun _ _ => by ring)

/-- For row indicators, the square of the mean over a fiber counts ordered
collisions. A collision has columns y,z,h(y)-t,h(z)-t, giving the desired
shift when h is multiplication by a power of two in ZMod (2^n). -/
theorem four_columns_mean {R G : Type*} [Fintype R] [Nonempty R] [Fintype G] [AddCommGroup G]
    (good : R → G → ℝ) (h : G → G) :
    (𝔼 x, 𝔼 y, good x y)^4 ≤
      𝔼 t, 𝔼 y, 𝔼 z, 𝔼 x, (good x y * good x (h y - t)) * (good x z * good x (h z - t)) := by
  let f (x : R) (t y : G) := good x y * good x (h y - t)
  have fiber (x : R) : (𝔼 t, 𝔼 y, f x t y) = (𝔼 y, good x y)^2 := by
    rw [Finset.expect_comm, sq, Fintype.expect_mul_expect]
    apply Finset.expect_congr rfl
    intro y _
    simp only [f, ← Finset.mul_expect]
    congr 1
    simp only [Fintype.expect_eq_sum_div_card]
    congr 1
    exact (Equiv.subLeft (h y)).sum_comp (good x)
  calc
    _ ≤ 𝔼 x, (𝔼 y, good x y)^4 := fourth_moment _
    _ ≤ 𝔼 x, 𝔼 t, (𝔼 y, f x t y)^2 := by
      apply Finset.expect_le_expect
      intro x _
      convert mean_square (fun t => 𝔼 y, f x t y) using 1
      rw [fiber]; ring
    _ = _ := by
      simp_rw [sq, Fintype.expect_mul_expect]
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro t _
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro y _
      rw [Finset.expect_comm]

/-- The maximum argument used with the trailing-zero moment in Lemma 4.1. -/
theorem exists_four_columns_weighted {I : Type*} [Fintype I] [Nonempty I] (q w : I → ℝ)
    {δ K : ℝ} (mass : δ^4 ≤ 𝔼 i, q i) (budget : (𝔼 i, w i) ≤ K)
    (pos : ∀ i, 0 < w i) (hq : ∀ i, 0 ≤ q i) :
    ∃ i, δ^4 * w i ≤ K * q i := by
  classical
  obtain ⟨best, _, maximum⟩ := Finset.exists_max_image Finset.univ (fun i => q i / w i)
    Finset.univ_nonempty
  have rate := div_nonneg (hq best) (pos best).le
  have bound : δ^4 ≤ q best / w best * K := calc
    _ ≤ _ := mass
    _ ≤ 𝔼 i, (q best / w best) * w i := Finset.expect_le_expect fun i _ =>
      (div_le_iff₀ (pos i)).mp (maximum i (Finset.mem_univ _))
    _ ≤ _ := by rw [← Finset.mul_expect]; exact mul_le_mul_of_nonneg_left budget rate
  refine ⟨best, ?_⟩
  rw [div_mul_eq_mul_div] at bound
  simpa only [mul_comm K] using (le_div_iff₀ (pos best)).mp bound

end OAI.Computability.MultitapeWeakETH

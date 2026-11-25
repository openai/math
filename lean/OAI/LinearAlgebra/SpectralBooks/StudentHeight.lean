import OAI.LinearAlgebra.SpectralBooks.NormalHinge
import OAI.LinearAlgebra.SpectralBooks.StudentEndpoints
import OAI.LinearAlgebra.SpectralBooks.StudentOptimizer
import OAI.LinearAlgebra.SpectralBooks.StudentTail

/-! # The Student bound from the spine-ball price inequality

Conditioning on the Gaussian spine radius evaluates each expected positive
part. At the optimizing height the Laplace transform term cancels the price of
the load, and size-biasing the radius leaves a Student upper tail.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

/-- Expected increase of the support of the spine ball on adding a tip of height `a`. -/
def spineHinge (q : ℕ) (a : ℝ) : ℝ :=
  ∫ h : ℝ, chiDensity q h * ∫ z : ℝ, max (a * z - h) 0 ∂gaussianReal 0 1

/-- Evaluating the radial and normal integrals leaves an exponential moment
and a size-biased Gaussian upper tail. -/
theorem spineHinge_eq {q : ℕ} (hq : 0 < q) {a : ℝ} (ha : 0 < a) :
    spineHinge q a =
      (a * (Real.sqrt (2 * Real.pi))⁻¹) * (1 + a⁻¹ ^ 2) ^ (-(q : ℝ) / 2) -
      chiMean q * studentTail (q + 1) (Real.sqrt ((q : ℝ) + 1) / a) := by
  have hd : (Real.sqrt ((q : ℝ) + 1)) ≠ 0 := by positivity
  have hratio : Real.sqrt ((q : ℝ) + 1) / a / Real.sqrt (↑(q + 1 : ℕ)) = a⁻¹ := by
    push_cast
    field_simp
  have hp (h : ℝ) : chiDensity q h * (∫ z, max (a * z - h) 0 ∂gaussianReal 0 1) =
      a * (Real.sqrt (2 * Real.pi))⁻¹ * (chiDensity q h * Real.exp (-(a⁻¹ ^ 2 * h ^ 2) / 2)) -
        chiMean q * (chiDensity (q+1) h * normalTail (a⁻¹ * h)) := by
    rw [normalHinge_integral a h ha, mul_sub, ← mul_assoc (chiMean q), ← chiDensity_sizeBias hq,
      show h / a = a⁻¹ * h by ring, mul_pow]
    ring
  simp only [spineHinge, hp, studentTail, hratio]
  rw [integral_sub ((integrable_chiDensity_laplace hq (sq_nonneg a⁻¹)).const_mul _)
      ((integrable_chiDensity_mul_normalTail (Nat.succ_pos q) a⁻¹).const_mul _),
    integral_const_mul, integral_const_mul, integral_chiDensity_laplace hq (sq_nonneg a⁻¹)]

theorem spineHinge_nonneg {q : ℕ} (hq : 0 < q) (a : ℝ) : 0 ≤ spineHinge q a :=
  integral_nonneg fun h ↦ mul_nonneg (chiDensity_nonneg hq h)
    (integral_nonneg fun _ ↦ le_max_right _ _)

theorem tendsto_spineHinge_zero {q : ℕ} (hq : 0 < q) :
    Tendsto (spineHinge q) (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun a : ℝ ↦ a * (Real.sqrt (2 * Real.pi))⁻¹) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuousWithinAt_id (s := Ioi 0) (x := (0 : ℝ))).tendsto.mul_const
      (Real.sqrt (2 * Real.pi))⁻¹
  apply tendsto_const_nhds.squeeze' hlim (Eventually.of_forall (spineHinge_nonneg hq))
  filter_upwards [self_mem_nhdsWithin] with a ha
  have hap : 0 < a := ha
  rw [spineHinge_eq hq hap]
  apply (sub_le_self _ (mul_nonneg (chiMean_pos hq).le (studentTail_nonneg _ _))).trans
  exact mul_le_of_le_one_right (by positivity)
    (Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg a⁻¹]) (by have := Nat.cast_nonneg (α := ℝ) q; linarith))

/-- The finite Student tail test for nonnegative loads, deduced from the
spine-ball price inequality for all positive choices of tip heights. -/
theorem student_bound_of_spine_price {ι : Type*} [Fintype ι] {q : ℕ} (hq : 0 < q)
    {L : ℝ} (hL : 0 ≤ L) {m : ι → ℝ} (hm : ∀ i, 0 ≤ m i) (hmL : ∀ i, m i ≤ L)
    (hprice : ∀ a : ι → ℝ, (∀ i, 0 < a i) →
      ∑ i, a i * m i ≤ L * Real.sqrt (2 * Real.pi) * (chiMean q + ∑ i, spineHinge q (a i))) :
    ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < m i),
      studentTail (q + 1) (Real.sqrt (((q : ℝ) + 1) * ((L / m i) ^ (2 / (q : ℝ)) - 1))) ≤ 1 := by
  classical
  obtain rfl | hL := hL.eq_or_lt
  · have hm0 (i : ι) : m i = 0 := le_antisymm (hmL i) (hm i)
    simp [hm0]
  let k := L * Real.sqrt (2 * Real.pi)
  have hk : 0 < k := by dsimp [k]; positivity
  apply student_bound_of_height (C := k * chiMean q) (cost := fun a ↦ k * spineHinge q a)
    (tailAtLoad := fun x ↦ studentTail (q + 1)
      (Real.sqrt (((q : ℝ) + 1) * ((L / x) ^ (2 / (q : ℝ)) - 1))))
    (mul_pos hk (chiMean_pos hq)) hL hm hmL
  · simpa only [mul_add, Finset.mul_sum, k] using hprice
  · simpa using (tendsto_spineHinge_zero hq).const_mul k
  · intro x hx hxL
    obtain ⟨a, ha, hcancel, hthreshold⟩ := exists_studentHeight hq hx hxL
    refine ⟨a, ha, ?_⟩
    rw [spineHinge_eq hq ha, hthreshold]
    have hid : k * (a * (Real.sqrt (2 * Real.pi))⁻¹ * (1 + a⁻¹ ^ 2) ^ (-(q : ℝ) / 2)) =
        a * x := by
      rw [← hcancel]
      calc
        _ = a * (L * (1 + a⁻¹ ^ 2) ^ (-(q : ℝ) / 2)) *
              (Real.sqrt (2 * Real.pi) * (Real.sqrt (2 * Real.pi))⁻¹) := by dsimp [k]; ring
        _ = _ := by rw [mul_inv_cancel₀ (by positivity), mul_one]
    rw [mul_sub k, hid]
    linarith only
  · apply (studentTail_continuous (Nat.succ_pos q)).continuousAt.comp_continuousWithinAt
    exact (continuousWithinAt_const.mul
      (((continuousWithinAt_const.div continuousWithinAt_id hL.ne').rpow_const
        (Or.inl (div_ne_zero hL.ne' hL.ne'))).sub continuousWithinAt_const)).sqrt

end

end

end SpectralBooks
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.TensorSpectrum.TagOptimized
open OAI.LinearAlgebra.TensorSpectrum
namespace OAI.LinearAlgebra.MatrixExponent.Integral
theorem tag_optimized_of_fiber_bounds
    {s : ℕ} (hs : 0 < s) (p : ℝ) (hp : 0 < p)
    (c : Fin s → ℝ) (hc : ∀ i, 0 < c i) (x : ℝ) (hx : 0 ≤ x)
    (hfinite : ∀ N : ℕ, 1 ≤ N → ∀ v : TagWords.CountVector s N,
      0 < (TagWords.fiber v).card →
      ((TagWords.fiber v).card : ℝ) ^ p * TagWords.countWeight c v ≤
        6 * x ^ N) :
    (∑ i, (c i) ^ (1 / p)) ^ p ≤ x := by
  classical
  let a : Fin s → ℝ := fun i => (c i) ^ (1 / p)
  have ha : ∀ i, 0 < a i := fun i => Real.rpow_pos_of_pos (hc i) _
  have haroot : ∀ i, (a i) ^ p = c i := by
    intro i
    simpa only [a, one_div] using Real.rpow_inv_rpow (hc i).le hp.ne'
  have hasum : 0 < ∑ i, a i := by
    let i₀ : Fin s := ⟨0, hs⟩
    exact (ha i₀).trans_le
      (Finset.single_le_sum (fun i _ => (ha i).le) (Finset.mem_univ i₀))
  apply le_of_pow_le_polynomial_mul_pow x ((∑ i, a i) ^ p) 6 ((s : ℝ) * p)
    hx (Real.rpow_nonneg hasum.le _) (by norm_num) (by positivity)
  intro N hN
  obtain ⟨v, hv, havg⟩ :=
    TagWords.exists_nonempty_fiberMass_ge_average (N := N) a hasum
  have hcount : 0 ≤ TagWords.countWeight a v :=
    Finset.prod_nonneg (fun i _ => pow_nonneg (ha i).le (v i).val)
  have hmass : 0 ≤ TagWords.fiberMass a v :=
    mul_nonneg (Nat.cast_nonneg _) hcount
  have hraw : (∑ i, a i) ^ N ≤
      ((N : ℝ) + 1) ^ s * TagWords.fiberMass a v := by
    have hden : 0 < ((N : ℝ) + 1) ^ s := by positivity
    simpa only [mul_comm] using (div_le_iff₀ hden).mp havg
  have hmasspow : (TagWords.fiberMass a v) ^ p =
      ((TagWords.fiber v).card : ℝ) ^ p * TagWords.countWeight c v := by
    unfold TagWords.fiberMass
    rw [Real.mul_rpow (Nat.cast_nonneg _) hcount,
      countWeight_rpow a (fun i => (ha i).le) v p]
    simp_rw [haroot]
  have hbound : (TagWords.fiberMass a v) ^ p ≤ 6 * x ^ N := by
    rw [hmasspow]
    exact hfinite N hN v (Finset.card_pos.mpr hv)
  have hraise := Real.rpow_le_rpow (pow_nonneg hasum.le N) hraw hp.le
  have hdenpow : (((N : ℝ) + 1) ^ s) ^ p =
      ((N : ℝ) + 1) ^ ((s : ℝ) * p) :=
    (Real.rpow_natCast_mul (by positivity) s p).symm
  calc
    ((∑ i, a i) ^ p) ^ N = ((∑ i, a i) ^ N) ^ p :=
      Real.rpow_pow_comm hasum.le p N
    _ ≤ (((N : ℝ) + 1) ^ s * TagWords.fiberMass a v) ^ p := hraise
    _ = ((N : ℝ) + 1) ^ ((s : ℝ) * p) * (TagWords.fiberMass a v) ^ p := by
      rw [Real.mul_rpow (by positivity) hmass, hdenpow]
    _ ≤ ((N : ℝ) + 1) ^ ((s : ℝ) * p) * (6 * x ^ N) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg (by positivity) _)
    _ = 6 * ((N : ℝ) + 1) ^ ((s : ℝ) * p) * x ^ N := by ring

end OAI.LinearAlgebra.MatrixExponent.Integral

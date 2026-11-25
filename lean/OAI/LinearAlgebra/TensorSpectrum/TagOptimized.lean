import OAI.LinearAlgebra.TensorSpectrum.TagWords
import OAI.LinearAlgebra.TensorSpectrum.TagGrowth

/-!
# Optimizing the finite-fiber tag bound

The hypothesis here is the numeric inequality for each actual nonempty word
fiber. Its tensor-theoretic proof belongs to the restriction construction.
Taking roots of the letter weights makes the largest fiber capture the desired
sum; the remaining count of possible fibers is only polynomial in the power.
-/

noncomputable section

open scoped BigOperators

namespace OAI.LinearAlgebra.TensorSpectrum

/-- A real power distributes over a finite product of nonnegative factors. -/
theorem finset_prod_rpow_nonneg {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (p : ℝ) (ha : ∀ i ∈ t, 0 ≤ a i) :
    (∏ i ∈ t, a i) ^ p = ∏ i ∈ t, (a i) ^ p := by
  classical
  revert ha
  induction t using Finset.induction_on with
  | empty => intro ha; simp
  | @insert i t hi ih =>
      intro ha
      have hai : 0 ≤ a i := ha i (Finset.mem_insert_self i t)
      have hat : ∀ j ∈ t, 0 ≤ a j :=
        fun j hj => ha j (Finset.mem_insert_of_mem hj)
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        Real.mul_rpow hai (Finset.prod_nonneg hat), ih hat]

/-- Powering a count weight is equivalent to powering its letter weights. -/
theorem countWeight_rpow {s N : ℕ} (a : Fin s → ℝ)
    (ha : ∀ i, 0 ≤ a i) (v : TagWords.CountVector s N) (p : ℝ) :
    (TagWords.countWeight a v) ^ p =
      TagWords.countWeight (fun i => (a i) ^ p) v := by
  classical
  unfold TagWords.countWeight
  rw [finset_prod_rpow_nonneg Finset.univ _ p
    (fun i _ => pow_nonneg (ha i) (v i).val)]
  apply Finset.prod_congr rfl
  intro i _
  exact (Real.rpow_pow_comm (ha i) p (v i).val).symm

/-- Optimized tag inequality from the finite-fiber inequalities. The constant
`5` and the polynomial number of possible count vectors disappear in the
tensor-power limit. The premise uses each fiber's actual finite cardinality. -/
theorem tag_optimized_of_fiber_bounds
    {s : ℕ} (hs : 0 < s) (p : ℝ) (hp : 0 < p)
    (c : Fin s → ℝ) (hc : ∀ i, 0 < c i) (x : ℝ) (hx : 0 ≤ x)
    (hfinite : ∀ N : ℕ, 1 ≤ N → ∀ v : TagWords.CountVector s N,
      0 < (TagWords.fiber v).card →
      ((TagWords.fiber v).card : ℝ) ^ p * TagWords.countWeight c v ≤
        5 * x ^ N) :
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
  apply le_of_pow_le_polynomial_mul_pow x ((∑ i, a i) ^ p) 5 ((s : ℝ) * p)
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
  have hbound : (TagWords.fiberMass a v) ^ p ≤ 5 * x ^ N := by
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
    _ ≤ ((N : ℝ) + 1) ^ ((s : ℝ) * p) * (5 * x ^ N) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg (by positivity) _)
    _ = 5 * ((N : ℝ) + 1) ^ ((s : ℝ) * p) * x ^ N := by ring

end OAI.LinearAlgebra.TensorSpectrum

import OAI.LinearAlgebra.FiniteFourier.StateCompression

/-! # Clearing a state resolvent by a reversed annihilating polynomial -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix Polynomial
open scoped Polynomial

variable {K : Type*} [Field K] {S I O : Type*} [Fintype S] [DecidableEq S]

/-- The reversal with respect to the specified degree. -/
noncomputable def reversedCoefficients (d : ℕ) (c : ℕ → K) : K[X] :=
  ∑ k ∈ Finset.range (d + 1), monomial (d - k) (c k)

/-- Weight each geometric partial sum by the corresponding reversed coefficient. -/
noncomputable def clearedWalkPolynomial (d : ℕ) (c : ℕ → K) (C : Matrix S S K)
    (T : Matrix S I K) (E : Matrix O S K) (D : Matrix O I K) : Matrix O I K[X] := fun o i =>
  ∑ k ∈ Finset.range (d + 1), monomial (d - k) (c k) * walkPolynomial k C T E D o i

theorem natDegree_reversedCoefficients_le (d : ℕ) (c : ℕ → K) :
    (reversedCoefficients d c).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro k _
  exact (natDegree_monomial_le _).trans (Nat.sub_le _ _)

theorem natDegree_clearedWalkPolynomial_le (d : ℕ) (c : ℕ → K) (C : Matrix S S K)
    (T : Matrix S I K) (E : Matrix O S K) (D : Matrix O I K) (o : O) (i : I) :
    (clearedWalkPolynomial d c C T E D o i).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  apply natDegree_mul_le.trans
  apply (Nat.add_le_add (natDegree_monomial_le _) (natDegree_walkPolynomial_le k C T E D o i)).trans
  exact (Nat.sub_add_cancel (by simpa using hk)).le

private theorem annihilator_geometric (z : K) (d : ℕ) (c : ℕ → K) (C : Matrix S S K)
    (hann : ∑ k ∈ Finset.range (d + 1), c k • C ^ k = 0)
    (hunit : IsUnit (1 - z • C).det) :
    ∑ k ∈ Finset.range (d + 1), (c k * z ^ (d - k)) •
        (∑ j ∈ Finset.range k, z ^ j • C ^ j) =
      (∑ k ∈ Finset.range (d + 1), c k * z ^ (d - k)) • (1 - z • C)⁻¹ := by
  let U := ∑ k ∈ Finset.range (d + 1), (c k * z ^ (d - k)) •
      (∑ j ∈ Finset.range k, z ^ j • C ^ j)
  let t := ∑ k ∈ Finset.range (d + 1), c k * z ^ (d - k)
  have h : U * (1 - z • C) = t • (1 : Matrix S S K) := by
    dsimp only [U, t]
    simp_rw [Matrix.sum_mul, Matrix.smul_mul, ← _root_.smul_pow, geom_sum_mul_neg,
      _root_.smul_pow, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
    suffices hzero : ∑ k ∈ Finset.range (d + 1), (c k * z ^ (d - k)) •
        (z ^ k • C ^ k) = 0 by rw [hzero, sub_zero]
    calc
      _ = ∑ k ∈ Finset.range (d + 1), z ^ d • (c k • C ^ k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [smul_smul, smul_smul, mul_assoc, ← pow_add,
          Nat.sub_add_cancel (by simpa using hk), mul_comm]
      _ = 0 := by rw [← Finset.smul_sum, hann, smul_zero]
  change U = t • (1 - z • C)⁻¹
  rw [← Matrix.mul_nonsing_inv_cancel_right (1 - z • C) U hunit, h, Matrix.smul_mul, one_mul]

/-- Evaluating the reversed annihilator clears the transfer at every scalar
for which the modified state pencil is invertible. -/
theorem eval_clearedWalkPolynomial {L : Type*} [Field L] (f : K →+* L) (z : L) (d : ℕ)
    (c : ℕ → K) (C : Matrix S S K) (T : Matrix S I K) (E : Matrix O S K) (D : Matrix O I K)
    (hann : ∑ k ∈ Finset.range (d + 1), c k • C ^ k = 0)
    (hunit : IsUnit (1 - z • C.map f).det) :
    (clearedWalkPolynomial d c C T E D).map (eval₂RingHom f z) =
      ((reversedCoefficients d c).eval₂ f z) •
        stateTransfer z (C.map f) (T.map f) (E.map f) (D.map f) := by
  let v := fun k => f (c k) * z ^ (d-k)
  have hsum : (clearedWalkPolynomial d c C T E D).map (eval₂RingHom f z) =
      ∑ k ∈ Finset.range (d + 1), v k • ((walkPolynomial k C T E D).map (eval₂RingHom f z)) := by
    ext o i
    simp [clearedWalkPolynomial, v, eval₂_finsetSum, eval₂_mul, Matrix.sum_apply]
  have hcoeff : (reversedCoefficients d c).eval₂ f z = ∑ k ∈ Finset.range (d + 1), v k := by
    simp [reversedCoefficients, v, eval₂_finsetSum]
  have hmap : ∑ k ∈ Finset.range (d + 1), f (c k) • (C.map f) ^ k = 0 := by
    ext a b
    have h := congrArg (fun M : Matrix S S K => f (M a b)) hann
    simpa [Matrix.sum_apply, ← Matrix.map_pow] using h
  rw [hsum, hcoeff, stateTransfer, smul_add]
  simp_rw [eval_walkPolynomial, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
  congr 1
  have shift (a : L) (M : Matrix S S L) :
      a • ((E.map f) * M * (z • T.map f)) = (E.map f) * (a • M) * (z • T.map f) := by
    rw [Matrix.mul_smul (E.map f) a M, Matrix.smul_mul]
  simp_rw [shift]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum]
  rw [show (∑ k ∈ Finset.range (d + 1), v k • ∑ j ∈ Finset.range k,
      z ^ j • C.map f ^ j) = (∑ k ∈ Finset.range (d + 1), v k) • (1 - z • C.map f)⁻¹
    from annihilator_geometric z d (f ∘ c) (C.map f) hmap hunit]

/-- Every formal state pencil is invertible over the rational function field,
since its polynomial determinant has constant term one. -/
theorem rational_pencil_unit (C : Matrix S S K) :
    IsUnit (1 - (RatFunc.X : RatFunc K) • C.map (RatFunc.C : K →+* RatFunc K)).det := by
  let φ := algebraMap K[X] (RatFunc K)
  have hc : C.charpolyRev ≠ 0 := by
    intro h
    simpa [h] using C.eval_charpolyRev
  have hp : (1 - (X : K[X]) • C.map Polynomial.C).map φ =
      1 - (RatFunc.X : RatFunc K) • C.map RatFunc.C := by
    ext i j
    simp [φ, Matrix.one_apply]
    exact mul_comm _ _
  apply isUnit_iff_ne_zero.mpr
  rw [← hp, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact RatFunc.algebraMap_ne_zero hc

/-- Reversing an annihilator of `C₀`, and normalizing at one, gives a split
whose rational remainder has rank at most the rank of the state change. -/
theorem general_transfer_split_of_cut [Fintype I] (C C₀ : Matrix S S K)
    (T : Matrix S I K) (E : Matrix O S K) (D : Matrix O I K) (g : K[X])
    (hg : aeval C₀ g = 0) (hone : g.eval 1 ≠ 0) :
    ∃ (B : K[X]) (Q : Matrix O I K[X]),
      B.eval 1 = 1 ∧ B.natDegree ≤ g.natDegree ∧
      (∀ o i, (Q o i).natDegree ≤ g.natDegree) ∧
      ((algebraMap K[X] (RatFunc K) B) • stateTransfer RatFunc.X (C.map RatFunc.C)
        (T.map RatFunc.C) (E.map RatFunc.C) (D.map RatFunc.C) -
        Q.map (algebraMap K[X] (RatFunc K))).rank ≤ (C - C₀).rank := by
  let c := fun k => (g.eval 1)⁻¹ * g.coeff k
  let d := g.natDegree
  let B := reversedCoefficients d c
  let Q := clearedWalkPolynomial d c C₀ T E D
  have hsum : ∑ k ∈ Finset.range (d + 1), c k = 1 := by
    have he := eval_eq_sum_range (p := g) (1 : K)
    simp only [one_pow, mul_one] at he
    simp only [c, ← Finset.mul_sum, d, ← he, inv_mul_cancel₀ hone]
  have hann : ∑ k ∈ Finset.range (d + 1), c k • C₀ ^ k = 0 := by
    rw [aeval_eq_sum_range] at hg
    simp only [c, mul_smul, ← Finset.smul_sum, d, hg, smul_zero]
  refine ⟨B, Q, ?_, natDegree_reversedCoefficients_le .., natDegree_clearedWalkPolynomial_le d c C₀ T E D, ?_⟩
  · simpa [B, reversedCoefficients, eval_finsetSum] using hsum
  · let φ := algebraMap K[X] (RatFunc K)
    let f : K →+* RatFunc K := RatFunc.C
    have hφ : eval₂RingHom f RatFunc.X = φ := by apply Polynomial.ringHom_ext <;> simp [f, φ]
    have hQ := eval_clearedWalkPolynomial f RatFunc.X d c C₀ T E D hann (rational_pencil_unit C₀)
    change Q.map (eval₂RingHom f RatFunc.X) = (eval₂RingHom f RatFunc.X) B • _ at hQ
    rw [hφ] at hQ
    change (φ B • stateTransfer _ _ _ _ _ - Q.map φ).rank ≤ _
    rw [hQ, ← smul_sub]
    have hr := rank_stateTransfer_sub_le RatFunc.X (C.map f) (C₀.map f) (T.map f)
      (E.map f) (D.map f) (rational_pencil_unit C) (rational_pencil_unit C₀)
    by_cases hB : φ B = 0
    · simp [hB]
    · rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hB)]
      apply hr.trans
      simpa [Matrix.map_sub _ (map_sub f)] using rank_map_le f (C - C₀)

end FiniteFourier
end LinearAlgebra
end OAI

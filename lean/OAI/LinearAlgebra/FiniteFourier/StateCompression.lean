import Mathlib
import OAI.LinearAlgebra.FiniteFourier.NilpotentChains

/-! # Finite-state transfer matrices and rank perturbations -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix
open scoped Polynomial

variable {K : Type*} [Field K] {S I O : Type*} [Fintype S] [DecidableEq S]

/-- The transfer of the state equation with formal length variable specialized to `z`. -/
noncomputable def stateTransfer (z : K) (C : Matrix S S K) (T : Matrix S I K)
    (E : Matrix O S K) (D : Matrix O I K) : Matrix O I K :=
  D + E * (1 - z • C)⁻¹ * (z • T)

/-- Difference of two inverse pencils at the same point. -/
theorem resolvent_sub (z : K) (C C₀ : Matrix S S K)
    (h : IsUnit (1 - z • C).det) (h₀ : IsUnit (1 - z • C₀).det) :
    (1 - z • C)⁻¹ - (1 - z • C₀)⁻¹ =
      (1 - z • C)⁻¹ * (z • (C - C₀)) * (1 - z • C₀)⁻¹ := by
  have diff : z • (C - C₀) = (1 - z • C₀) - (1 - z • C) := by
    rw [smul_sub]
    abel
  rw [diff, mul_sub, sub_mul, Matrix.mul_nonsing_inv_cancel_right _ _ h₀,
    Matrix.nonsing_inv_mul _ h, one_mul]

/-- Input and output maps preserve the rank bound of a change of state matrix. -/
theorem rank_stateTransfer_sub_le [Fintype I] (z : K) (C C₀ : Matrix S S K)
    (T : Matrix S I K) (E : Matrix O S K) (D : Matrix O I K)
    (h : IsUnit (1 - z • C).det) (h₀ : IsUnit (1 - z • C₀).det) :
    (stateTransfer z C T E D - stateTransfer z C₀ T E D).rank ≤ (C - C₀).rank := by
  simp only [stateTransfer, add_sub_add_left_eq_sub, ← Matrix.sub_mul, ← Matrix.mul_sub,
    resolvent_sub z C C₀ h h₀]
  apply (Matrix.rank_mul_le_left _ _).trans
  apply (Matrix.rank_mul_le_right _ _).trans
  apply (Matrix.rank_mul_le_left _ _).trans
  apply (Matrix.rank_mul_le_right _ _).trans
  by_cases hz : z = 0
  · simp [hz]
  · exact (Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hz)).le

/-- Over a field extension a column-space factorization still has the same inner size. -/
theorem rank_map_le {L : Type*} [Field L] [Fintype I] [Fintype O]
    (f : K →+* L) (M : Matrix O I K) : (M.map f).rank ≤ M.rank := by
  classical
  let W := LinearMap.range M.mulVecLin
  let v := Module.finBasis K W
  let i := Pi.basisFun K I
  let o := Pi.basisFun K O
  let A := W.subtype.toMatrix v o
  let B := M.mulVecLin.rangeRestrict.toMatrix i v
  have hfac : A * B = M := by
    dsimp only [A, B]
    rw [← LinearMap.toMatrix_comp]
    change M.mulVecLin.toMatrix (Pi.basisFun K I) (Pi.basisFun K O) = M
    exact LinearMap.toMatrix'_toLin' M
  have hm : (A.map f * B.map f) = M.map f := by rw [← Matrix.map_mul, hfac]
  rw [← hm]
  exact (Matrix.rank_mul_le_right _ _).trans (by simpa [W, Matrix.rank] using
    (Matrix.rank_le_card_height (B.map f)))

/-- A nilpotent pencil has a finite geometric resolvent at every parameter. -/
theorem resolvent_of_pow_eq_zero (z : K) (C : Matrix S S K) (b : ℕ) (h : C ^ b = 0) :
    (1 - z • C)⁻¹ = ∑ j ∈ Finset.range b, z ^ j • C ^ j := by
  apply Matrix.inv_eq_left_inv
  simp_rw [← smul_pow]
  rw [geom_sum_mul_neg, smul_pow, h, smul_zero, sub_zero]

/-- The transfer coefficients from walks using at most `b` states. -/
noncomputable def walkPolynomial (b : ℕ) (C : Matrix S S K) (T : Matrix S I K)
    (E : Matrix O S K) (D : Matrix O I K) : Matrix O I K[X] := fun o i =>
  Polynomial.C (D o i) + ∑ j ∈ Finset.range b,
    Polynomial.monomial (j + 1) ((E * C ^ j * T) o i)

theorem natDegree_walkPolynomial_le (b : ℕ) (C : Matrix S S K) (T : Matrix S I K)
    (E : Matrix O S K) (D : Matrix O I K) (o : O) (i : I) :
    ((walkPolynomial b C T E D) o i).natDegree ≤ b := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact (Polynomial.natDegree_monomial_le _).trans (Finset.mem_range.mp hj)

/-- Evaluation of the truncation is the corresponding geometric partial sum. -/
theorem eval_walkPolynomial {L : Type*} [Field L] (f : K →+* L) (z : L)
    (b : ℕ) (C : Matrix S S K) (T : Matrix S I K) (E : Matrix O S K) (D : Matrix O I K) :
    (walkPolynomial b C T E D).map (Polynomial.eval₂RingHom f z) =
      D.map f + E.map f * (∑ j ∈ Finset.range b, z ^ j • (C.map f) ^ j) * (z • T.map f) := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  ext o i
  simp only [Matrix.map_apply, walkPolynomial, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_add, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_C, Polynomial.eval₂_monomial, Matrix.add_apply, Matrix.sum_apply,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.smul_apply, smul_eq_mul]
  apply congrArg (f (D o i) + ·)
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.map_pow, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, pow_succ]
  ring

/-- For a nilpotent state matrix the walk polynomial gives the entire transfer. -/
theorem walkPolynomial_eq_transfer {L : Type*} [Field L] (f : K →+* L) (z : L)
    (b : ℕ) (C : Matrix S S K) (T : Matrix S I K) (E : Matrix O S K) (D : Matrix O I K)
    (h : C ^ b = 0) :
    (walkPolynomial b C T E D).map (Polynomial.eval₂RingHom f z) =
      stateTransfer z (C.map f) (T.map f) (E.map f) (D.map f) := by
  rw [eval_walkPolynomial, stateTransfer, resolvent_of_pow_eq_zero z _ b]
  rw [← Matrix.map_pow, h]
  simp

private theorem eval₂_C_X : Polynomial.eval₂RingHom (RatFunc.C : K →+* RatFunc K) RatFunc.X =
    algebraMap K[X] (RatFunc K) := by
  apply Polynomial.ringHom_ext <;> simp

private theorem nilpotentPencilUnit {L : Type*} [Field L] (f : K →+* L) (z : L)
    (C : Matrix S S K) (h : IsNilpotent C) : IsUnit (1 - z • C.map f).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply IsNilpotent.isUnit_one_sub
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [smul_pow, ← Matrix.map_pow, hn]; simp⟩

/-- A nilpotent state correction gives the manuscript's split with `B=1`.
The remainder is itself polynomial and therefore regular at both zero and one. -/
theorem nilpotent_transfer_split_of_cut [Fintype I] (C C₀ : Matrix S S K) (T : Matrix S I K)
    (E : Matrix O S K) (D : Matrix O I K) (b : ℕ) (hC : IsNilpotent C) (h₀ : C₀ ^ b = 0) :
    ∃ Q R : Matrix O I K[X],
      stateTransfer RatFunc.X (C.map RatFunc.C) (T.map RatFunc.C) (E.map RatFunc.C)
        (D.map RatFunc.C) = Q.map (algebraMap K[X] (RatFunc K)) +
          R.map (algebraMap K[X] (RatFunc K)) ∧
      (∀ o i, (Q o i).natDegree ≤ b) ∧
      (R.map (algebraMap K[X] (RatFunc K))).rank ≤ (C - C₀).rank := by
  obtain ⟨n, hn⟩ := hC
  let f : K[X] →+* RatFunc K := algebraMap _ _
  let Q := walkPolynomial b C₀ T E D
  let P := walkPolynomial n C T E D
  have hP : P.map f = stateTransfer RatFunc.X (C.map RatFunc.C) (T.map RatFunc.C)
      (E.map RatFunc.C) (D.map RatFunc.C) := by
    simpa only [P, f, eval₂_C_X] using walkPolynomial_eq_transfer RatFunc.C RatFunc.X n C T E D hn
  have hQ : Q.map f = stateTransfer RatFunc.X (C₀.map RatFunc.C) (T.map RatFunc.C)
      (E.map RatFunc.C) (D.map RatFunc.C) := by
    simpa only [Q, f, eval₂_C_X] using walkPolynomial_eq_transfer RatFunc.C RatFunc.X b C₀ T E D h₀
  refine ⟨Q, P - Q, ?_, natDegree_walkPolynomial_le b C₀ T E D, ?_⟩
  · change _ = Q.map f + (P - Q).map f
    rw [Matrix.map_sub _ (map_sub f), ← hP]
    abel
  · change ((P - Q).map f).rank ≤ _
    rw [Matrix.map_sub _ (map_sub f), hP, hQ]
    apply (rank_stateTransfer_sub_le _ _ _ _ _ _
      (nilpotentPencilUnit _ _ _ ⟨n, hn⟩) (nilpotentPencilUnit _ _ _ ⟨b, h₀⟩)).trans
    simpa only [Matrix.map_sub _ (map_sub RatFunc.C)] using rank_map_le RatFunc.C (C - C₀)

/-- The nilpotent case of state compression. The transfer is a polynomial matrix
of degree at most `b` plus a polynomial remainder of rational rank at most `S/b`. -/
theorem nilpotent_state_compression [Fintype I] (C : Matrix S S K) (T : Matrix S I K)
    (E : Matrix O S K) (D : Matrix O I K) (hC : IsNilpotent C) {b : ℕ} (hb : 0 < b) :
    ∃ Q R : Matrix O I K[X],
      stateTransfer RatFunc.X (C.map RatFunc.C) (T.map RatFunc.C) (E.map RatFunc.C)
        (D.map RatFunc.C) = Q.map (algebraMap K[X] (RatFunc K)) +
          R.map (algebraMap K[X] (RatFunc K)) ∧
      (∀ o i, (Q o i).natDegree ≤ b) ∧
      (R.map (algebraMap K[X] (RatFunc K))).rank * b ≤ Fintype.card S := by
  obtain ⟨C₀, h₀, hcut⟩ := exists_nilpotent_matrix_cut C hC b hb
  obtain ⟨Q, R, hsplit, hdeg, hrank⟩ := nilpotent_transfer_split_of_cut C C₀ T E D b hC h₀
  exact ⟨Q, R, hsplit, hdeg, (Nat.mul_le_mul_right b hrank).trans hcut⟩

end FiniteFourier
end LinearAlgebra
end OAI

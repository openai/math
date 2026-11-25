import OAI.LinearAlgebra.FiniteFourier.BatchedLinearLower

/-! # A two-minor obstruction with simultaneous errors

Restrict to common rows and two disjoint column lists. Each direct input readout
can contribute to at most one of the two restricted ranks. A single product of
determinants makes this obstruction valid on the joint Zariski closure.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier
open Matrix MvPolynomial
open scoped Classical
noncomputable section

theorem matrix_rank_add_le {K I O : Type*} [Field K] [Fintype I] [Fintype O]
    (A B : Matrix O I K) : (A+B).rank ≤ A.rank + B.rank := by
  change Module.finrank K (LinearMap.range (A+B).mulVecLin) ≤ _
  rw [Matrix.mulVecLin_add A B]
  exact (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank A.mulVecLin.range B.mulVecLin.range)

private theorem rank_le_entries {K I O : Type*} [Field K] [Fintype I] [Fintype O]
    (Z : Matrix O I K) :
    Z.rank ≤ matrixEntryCount Z := by
  classical
  unfold matrixEntryCount
  let entries := Finset.univ.filter (fun ij : O × I => Z ij.1 ij.2 ≠ 0)
  apply (Z.rank_le_card_of_support_subset (entries.image Prod.fst) ?_).trans Finset.card_image_le
  intro o ho
  have h : ∃ i, Z o i ≠ 0 := by
    by_contra! hz
    exact ho (funext hz)
  obtain ⟨i, hi⟩ := h
  exact Finset.mem_image.mpr ⟨(o,i), by simpa [entries] using hi, rfl⟩

private theorem Feedback.two_read_ranks {K I O Q : Type*} [Field K] [Fintype I]
    [Fintype Q] {s : ℕ} (F : Feedback K I O s) (row : Q → O) (a b : Q → I)
    (hab : ∀ i j, a i ≠ b j) :
    (F.readInput.submatrix row a).rank + (F.readInput.submatrix row b).rank ≤ Fintype.card Q := by
  let onLeft (q : Q) := ∃ i, (F.readInput (row q) (a i)) ≠ 0
  have ha := (F.readInput.submatrix row a).rank_le_card_of_support_subset
    (Finset.univ.filter onLeft) (by
      intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra h
      apply hq
      funext i
      exact not_ne_iff.mp fun hi => h ⟨i, hi⟩)
  have hb := (F.readInput.submatrix row b).rank_le_card_of_support_subset
    (Finset.univ.filter (fun q => ¬onLeft q)) (by
      intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨i, hi⟩
      apply hq
      funext j
      change F.readInput (row q) (b j) = 0
      cases h : F.output (row q) with
      | zero => simp [Feedback.readInput, Feedback.readRow, h] at hi
      | scaled c w =>
        cases w with
        | inr => simp [Feedback.readInput, Feedback.readRow, h] at hi
        | inl k =>
          by_cases he : k = a i
          · subst k
            simp [Feedback.readInput, Feedback.readRow, h, (hab i j).symm]
          · simp [Feedback.readInput, Feedback.readRow, h, Ne.symm he] at hi)
  simpa only [Finset.card_filter_add_card_filter_not, Finset.card_univ] using Nat.add_le_add ha hb

private theorem two_minor_rank_budget {K I O Q : Type*} [Field K] [Fintype I]
    [Fintype O] [Fintype Q] {s : ℕ} (F : Feedback K I O s) (B Z : Matrix O I K)
    (row : Q → O) (a b : Q → I) (hab : ∀ i j, a i ≠ b j) :
    ((F.matrix+B+Z).submatrix row a).rank + ((F.matrix+B+Z).submatrix row b).rank ≤
    Fintype.card Q + 2 * (s + B.rank + Z.rank) := by
  let state := F.readState * (1 - F.stateMatrix)⁻¹ * F.inputMatrix
  have hs : state.rank ≤ s := (rank_mul_le_left _ _).trans
    (by simpa using (F.readState * (1 - F.stateMatrix)⁻¹).rank_le_card_width)
  have panel (t : Q → I) : ((F.matrix+B+Z).submatrix row t).rank ≤
      (F.readInput.submatrix row t).rank + (s + B.rank + Z.rank) := by
    have eq : (F.matrix+B+Z).submatrix row t = F.readInput.submatrix row t +
        (state+B+Z).submatrix row t := by
      ext i j
      change ((F.readInput _ _ + state _ _) + B _ _) + Z _ _ = _
      simp [Matrix.submatrix_apply, add_assoc]
    rw [eq]
    apply (matrix_rank_add_le ..).trans
    apply Nat.add_le_add_left
    apply (Matrix.rank_submatrix_le ..).trans
    have h₁ := matrix_rank_add_le state B
    have h₂ := matrix_rank_add_le (state+B) Z
    omega
  have h := F.two_read_ranks row a b hab
  have ha := panel a
  have hb := panel b
  omega

private def minorPolynomial {L I O Q : Type*} [Field L] [Fintype Q] [DecidableEq Q]
    (row : Q → O) (col : Q → I) : MvPolynomial (O × I) L :=
  (Matrix.of fun i j => (X (row i, col j) : MvPolynomial (O × I) L)).det

private theorem eval_minorPolynomial {L I O Q : Type*} [Field L] [Fintype Q] [DecidableEq Q]
    (A : Matrix O I L) (row : Q → O) (col : Q → I) :
    eval (fun ij => A ij.1 ij.2) (minorPolynomial row col) = (A.submatrix row col).det := by
  unfold minorPolynomial
  rw [RingHom.map_det]
  congr 1
  ext i j
  change eval (fun ij : O × I => A ij.1 ij.2) (X (row i, col j)) = A (row i) (col j)
  simp

private theorem two_minors_vanish {L I O Q : Type*} [Field L] [Fintype I] [Fintype O]
    [Fintype Q] [DecidableEq Q] {s : ℕ} {r t : ℝ} (small : 2 * (s + r + t) < Fintype.card Q)
    (row : Q → O) (a b : Q → I) (hab : ∀ i j, a i ≠ b j) (A B Z : Matrix O I L)
    (ha : FeedbackAtMost A s) (hb : (B.rank : ℝ) ≤ r)
    (hz : (matrixEntryCount Z : ℝ) ≤ t) :
    eval (fun ij => (A+B+Z) ij.1 ij.2) (minorPolynomial row a * minorPolynomial row b) = 0 := by
  obtain ⟨k, hk, F, _, rfl⟩ := ha
  rw [map_mul, eval_minorPolynomial, eval_minorPolynomial]
  by_contra hne
  obtain ⟨h₀,h₁⟩ := mul_ne_zero_iff.mp hne
  have bound := two_minor_rank_budget F B Z row a b hab
  rw [rank_of_det_ne_zero h₀, rank_of_det_ne_zero h₁] at bound
  have rankZ : (Z.rank : ℝ) ≤ t := (Nat.cast_le.mpr (rank_le_entries Z)).trans hz
  have budget : Fintype.card Q ≤ 2 * (k + B.rank + Z.rank) := by omega
  have budget' : (Fintype.card Q : ℝ) ≤ 2 * ((k : ℝ) + B.rank + Z.rank) := by exact_mod_cast budget
  have hk' : (k : ℝ) ≤ s := Nat.cast_le.mpr hk
  exact (not_le_of_gt small) (budget'.trans (by gcongr))

private theorem map_submatrix_det_ne_zero {K L I O Q : Type*} [Field K] [Field L]
    [Fintype Q] [DecidableEq Q] (f : K →+* L) (M : Matrix O I K) (row : Q → O) (col : Q → I)
    (hd : (M.submatrix row col).det ≠ 0) : ((M.map f).submatrix row col).det ≠ 0 := by
  change (f.mapMatrix (M.submatrix row col)).det ≠ 0
  rw [← f.map_det]
  exact (map_ne_zero_iff f f.injective).mpr hd

/-- Each minor uses the same rows. The column lists are mutually disjoint. -/
theorem JointErrorBorderAtMost.two_minors {K I O Q : Type*} [Field K] [Fintype I]
    [Fintype O] [Fintype Q] [DecidableEq Q] {s : ℕ} {r t : ℝ} {M : Matrix O I K}
    (h : JointErrorBorderAtMost M s r t) (row : Q → O) (a b : Q → I)
    (hab : ∀ i j, a i ≠ b j) (ha : (M.submatrix row a).det ≠ 0)
    (hb : (M.submatrix row b).det ≠ 0) : (Fintype.card Q : ℝ) ≤ 2 * (s + r + t) := by
  by_contra! hsmall
  have test := h (minorPolynomial row a * minorPolynomial row b)
    (two_minors_vanish hsmall row a b hab)
  let f := algebraMap K (AlgebraicClosure K)
  change eval (fun ij : O × I => (M.map f) ij.1 ij.2)
    (minorPolynomial row a * minorPolynomial row b) = 0 at test
  rw [map_mul, eval_minorPolynomial, eval_minorPolynomial] at test
  exact (mul_ne_zero (map_submatrix_det_ne_zero f M row a ha)
    (map_submatrix_det_ne_zero f M row b hb)) test

/-- One row and two distinct columns per Fourier block already suffice uniformly for
bounded orders, with both errors operating across the entire batch. -/
theorem batchFourier_two_minors {K : Type*} [Field K] {J n s : ℕ}
    (B : Fin J → FourierBlock K n) (hn : 2 ≤ n) {r t : ℝ}
    (h : JointErrorBorderAtMost (batchMatrix B) s r t) : (J : ℝ) ≤ 2 * (s + r + t) := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let col (i : Fin n) (j : Fin J) := (i,j)
  have hd (i : Fin n) : ((batchMatrix B).submatrix (col a) (col i)).det ≠ 0 := by
    have eq : (batchMatrix B).submatrix (col a) (col i) =
        Matrix.diagonal (fun j => (B j).matrix a i) := by
      ext j k
      by_cases hjk : j = k <;> simp [hjk, batchMatrix, col, Matrix.blockDiagonal_apply, Matrix.diagonal]
    rw [eq, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => (B j).entry_ne_zero _ _
  simpa using h.two_minors (col a) (col a) (col b)
    (fun j k he => by have := congrArg (fun x : Fin n × Fin J => x.1.val) he; simp [a,b,col] at this)
    (hd a) (hd b)

end
end FiniteFourier
end LinearAlgebra
end OAI

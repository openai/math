import OAI.LinearAlgebra.FiniteFourier.FeedbackBorder
import OAI.LinearAlgebra.FiniteFourier.Transform
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # A polynomial obstruction to fewer states than independent dense outputs

If every matrix entry is nonzero, direct input readout is impossible when
there are at least two inputs. Every output then factors through a state.
The product of all matrix entries times a maximal minor detects this
alternative in Zariski closure.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Matrix MvPolynomial

variable {I O K : Type*} [Field K] [Fintype I] [Fintype O] [Nontrivial I]

omit [Fintype O] in
/-- A dense feedback matrix factors through its state space. -/
theorem Feedback.readInput_eq_zero_of_dense {s : ℕ} (f : Feedback K I O s)
    (h : ∀ o i, f.matrix o i ≠ 0) : f.readInput = 0 := by
  classical
  ext o i
  cases hout : f.output o with
  | zero => simp [Feedback.readInput, Feedback.readRow, hout]
  | scaled c w =>
    cases w with
    | inr j => simp [Feedback.readInput, Feedback.readRow, hout]
    | inl k =>
      obtain ⟨j, hj⟩ := exists_ne k
      have hread := f.matrix_mulVec_apply (Pi.single j 1) o
      simp [hout, Matrix.mulVec_single, hj.symm] at hread
      exact False.elim ((h o j) hread)

omit [Fintype O] in
/-- Every full-support feedback matrix has rank at most its number of states. -/
theorem Feedback.rank_le_of_dense {s : ℕ} (f : Feedback K I O s)
    (h : ∀ o i, f.matrix o i ≠ 0) : f.matrix.rank ≤ s := by
  have h0 := f.readInput_eq_zero_of_dense h
  rw [Feedback.matrix, h0, zero_add]
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using (f.readState * (1 - f.stateMatrix)⁻¹).rank_le_card_width)

/-- The polynomial tested on the feedback matrices. `D` is any fixed right
factor, chosen as a right inverse when separating a particular target. -/
def denseMinor [DecidableEq O] (D : Matrix I O K) : MvPolynomial (O × I) K :=
  let H : Matrix O O (MvPolynomial (O × I) K) :=
    Matrix.of fun a b => ∑ i, X (a, i) * C (D i b)
  H.det * ∏ o : O, ∏ i : I, X (o, i)

omit [Nontrivial I] in
theorem eval_denseMinor [DecidableEq O] (D : Matrix I O K) (M : Matrix O I K) :
    eval (fun p : O × I => M p.1 p.2) (denseMinor D) =
      (M * D).det * ∏ o, ∏ i, M o i := by
  let e := eval (fun p : O × I => M p.1 p.2)
  simp only [denseMinor, map_mul, map_prod, eval_X]
  congr 1
  change e _ = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.mul_apply, e]

theorem denseMinor_vanishes [DecidableEq O] {s : ℕ} (f : Feedback K I O s)
    (hs : s < Fintype.card O) (D : Matrix I O K) :
    eval (fun p : O × I => f.matrix p.1 p.2) (denseMinor D) = 0 := by
  classical
  rw [eval_denseMinor]
  by_cases h : ∀ o i, f.matrix o i ≠ 0
  · apply mul_eq_zero_of_left
    by_contra hn
    have hr := Matrix.rank_of_det_ne_zero hn
    exact (not_lt_of_ge ((Matrix.rank_mul_le_left f.matrix D).trans (f.rank_le_of_dense h)))
      (by rwa [hr])
  · push Not at h
    obtain ⟨o, i, hzero⟩ := h
    have hrow : ∏ j, f.matrix o j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hzero
    rw [Finset.prod_eq_zero (Finset.mem_univ o) hrow, mul_zero]

/-- A dense matrix with a right inverse needs at least one state per output,
even after extending the field and taking Zariski closure. -/
theorem GeometricBorderAtMost.card_le_of_dense {M : Matrix O I K} {S : ℕ}
    (hborder : GeometricBorderAtMost M S) (hdense : ∀ o i, M o i ≠ 0)
    (D : Matrix I O K) [DecidableEq O] (hD : M * D = 1) : Fintype.card O ≤ S := by
  classical
  by_contra! hS
  let f := algebraMap K (AlgebraicClosure K)
  have h := hborder (denseMinor (D.map f)) (by
    rintro A ⟨s, hs, c, _, rfl⟩
    exact denseMinor_vanishes c (hs.trans_lt hS) _)
  change eval (fun p : O × I => (M.map f) p.1 p.2) (denseMinor (D.map f)) = 0 at h
  rw [eval_denseMinor, ← Matrix.map_mul, hD, Matrix.map_one _ (map_zero f) (map_one f),
    Matrix.det_one, one_mul] at h
  exact (Finset.prod_ne_zero_iff.mpr (fun o _ => Finset.prod_ne_zero_iff.mpr
    (fun i _ => (map_ne_zero_iff f f.injective).mpr (hdense o i)))) h

/-- Absolute linear lower bounds for both Fourier directions in geometric border.
This is also the small-order input to the logarithmic lower bound. -/
theorem fourier_border_card_le (G K : Type*) [AddCommGroup G] [Fintype G] [Field K]
    (had : Admissible G K) (hN : 2 ≤ Fintype.card G) (S : ℕ) :
    (GeometricBorderAtMost (fourierMatrix G K) S → Fintype.card G ≤ S) ∧
    (GeometricBorderAtMost (inverseFourierMatrix G K) S → Fintype.card G ≤ S) := by
  classical
  let : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp hN
  let : Nontrivial (Character G K) := Fintype.one_lt_card_iff_nontrivial.mp
    (by rwa [card_character G K had])
  constructor
  · intro h
    rw [← card_character G K had]
    exact h.card_le_of_dense (fun χ g => Units.ne_zero _) _ (fourier_mul_inverse G K had)
  · intro h
    exact h.card_le_of_dense (fun g χ => mul_ne_zero (inv_ne_zero had.1) (Units.ne_zero _))
      _ (inverse_mul_fourier G K had)

end

end

end FiniteFourier
end LinearAlgebra
end OAI

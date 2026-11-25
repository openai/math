import OAI.LinearAlgebra.FiniteFourier.Feedback.FeedbackTransfer
import OAI.LinearAlgebra.FiniteFourier.RankSpecialization
import OAI.LinearAlgebra.FiniteFourier.NilpotentChains
import OAI.LinearAlgebra.FiniteFourier.CompressionPolynomial

/-! # Polynomial compression of a binary feedback transfer

Subtracting a polynomial matrix from a polynomial multiple of the transfer preserves
its regular specializations. Cutting the state matrix to a nilpotent matrix of index
at most `b` produces a polynomial part of degree at most `b`.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Feedback

open Matrix Polynomial
noncomputable section

variable {K I O : Type*} [Field K] {s : ℕ} (F : Feedback K I O s)

/-- The rational remainder after clearing by `B` and extracting the polynomial part `Q`. -/
def residual (B : K[X]) (Q : Matrix O I K[X]) : Matrix O I (RatFunc K) :=
  algebraMap K[X] (RatFunc K) B • F.rationalTransfer -
    Q.map (algebraMap K[X] (RatFunc K))

/-- A common numerator of the remainder with the original state determinant as denominator. -/
def residualNumer (B : K[X]) (Q : Matrix O I K[X]) : Matrix O I K[X] :=
  B • F.transferNumer - F.transferDenom • Q

variable (B : K[X]) (Q : Matrix O I K[X])

theorem residual_eq_quotient :
    F.residual B Q = rationalQuotient (F.residualNumer B Q) F.transferDenom := by
  have hd := RatFunc.algebraMap_ne_zero F.transferDenom_ne_zero
  ext o i
  simp only [residual, residualNumer, rationalTransfer, rationalQuotient, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_sub, map_mul]
  field_simp

/-- At any point where the state determinant survives, the individual reduced
denominators of the remainder survive as well. -/
theorem residual_regularAt {z : K} (hz : F.transferDenom.eval z ≠ 0) (o : O) (i : I) :
    ((F.residual B Q) o i).denom.eval z ≠ 0 := by
  rw [F.residual_eq_quotient B Q]
  obtain ⟨d, hd⟩ := RatFunc.denom_div_dvd (F.residualNumer B Q o i) F.transferDenom
  intro hr
  exact hz (by rw [hd, eval_mul]; exact mul_eq_zero_of_left hr _)

theorem residual_regular_zero (o : O) (i : I) :
    ((F.residual B Q) o i).denom.eval 0 ≠ 0 :=
  F.residual_regularAt B Q (by simp) o i

theorem residual_regular_one (h : F.Regular) (o : O) (i : I) :
    ((F.residual B Q) o i).denom.eval 1 ≠ 0 :=
  F.residual_regularAt B Q (by rwa [eval_one_transferDenom]) o i

theorem eval_residual_eq_quotientAt {z : K} (hz : F.transferDenom.eval z ≠ 0) :
    (F.residual B Q).map (RatFunc.eval (RingHom.id K) z) =
      quotientAt (F.residualNumer B Q) F.transferDenom z := by
  ext o i
  have h := (RatFunc.num_mul_eq_mul_denom_iff F.transferDenom_ne_zero).mpr
    (congrFun (congrFun (F.residual_eq_quotient B Q) o) i)
  have he := congrArg (eval z) h
  simp only [eval_mul] at he
  exact (div_eq_div_iff (F.residual_regularAt B Q hz o i) hz).mpr he

/-- Regular evaluation commutes with the polynomial compression identity. -/
theorem eval_residual {z : K} (hz : F.transferDenom.eval z ≠ 0) :
    (F.residual B Q).map (RatFunc.eval (RingHom.id K) z) =
      B.eval z • F.rationalTransfer.map (RatFunc.eval (RingHom.id K) z) -
        Q.map (evalRingHom z) := by
  rw [F.eval_residual_eq_quotientAt B Q hz]
  ext o i
  simp only [quotientAt, residualNumer, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    eval_sub, eval_mul, Matrix.map_apply, coe_evalRingHom, F.eval_rationalTransfer_entry hz]
  field_simp

theorem eval_zero_residual :
    (F.residual B Q).map (RatFunc.eval (RingHom.id K) 0) =
      B.eval 0 • F.readInput - Q.map (evalRingHom 0) := by
  rw [F.eval_residual B Q (by simp), F.eval_zero_rationalTransfer]

theorem eval_one_residual (h : F.Regular) :
    (F.residual B Q).map (RatFunc.eval (RingHom.id K) 1) =
      B.eval 1 • F.matrix - Q.map (evalRingHom 1) := by
  rw [F.eval_residual B Q (by rwa [eval_one_transferDenom]), F.eval_one_rationalTransfer h]

theorem rank_eval_residual_le [Fintype O] [Fintype I] {z : K}
    (hz : F.transferDenom.eval z ≠ 0) :
    ((F.residual B Q).map (RatFunc.eval (RingHom.id K) z)).rank ≤ (F.residual B Q).rank := by
  rw [F.eval_residual_eq_quotientAt B Q hz, F.residual_eq_quotient B Q]
  exact rank_quotientAt_le _ _ _ hz

/-- An annihilator of a perturbed state matrix supplies a normalized compression
of the original feedback system, with the state-change rank as its error bound. -/
theorem general_residual_split_of_cut [Fintype I] (C₀ : Matrix (Fin s) (Fin s) K)
    (g : K[X]) (hg : aeval C₀ g = 0) (hone : g.eval 1 ≠ 0) :
    ∃ (B : K[X]) (Q : Matrix O I K[X]), B.eval 1 = 1 ∧ B.natDegree ≤ g.natDegree ∧
      (∀ o i, (Q o i).natDegree ≤ g.natDegree) ∧
      (F.residual B Q).rank ≤ (F.stateMatrix - C₀).rank := by
  obtain ⟨B, Q, hB1, hB, hQ, h⟩ := general_transfer_split_of_cut F.stateMatrix C₀
    F.inputMatrix F.readState F.readInput g hg hone
  refine ⟨B, Q, hB1, hB, hQ, ?_⟩
  simpa only [residual, F.rationalTransfer_eq_resolvent, stateTransfer] using h

/-- Replacing the original state matrix by a nilpotent one gives a degree-`b`
polynomial transfer and a remainder of rank bounded by the rank of the cut. -/
theorem nilpotent_residual_split [Fintype I] (C₀ : Matrix (Fin s) (Fin s) K) (b : ℕ)
    (h₀ : C₀ ^ b = 0) :
    ∃ Q : Matrix O I K[X], (∀ o i, (Q o i).natDegree ≤ b) ∧
      (F.residual 1 Q).rank ≤ (F.stateMatrix - C₀).rank := by
  let f := (RatFunc.C : K →+* RatFunc K)
  let z := (RatFunc.X : RatFunc K)
  let Q := walkPolynomial b C₀ F.inputMatrix F.readState F.readInput
  refine ⟨Q, natDegree_walkPolynomial_le b C₀ F.inputMatrix F.readState F.readInput, ?_⟩
  have φ : eval₂RingHom f z = algebraMap K[X] (RatFunc K) := by
    apply Polynomial.ringHom_ext <;> simp [f, z]
  have hQ := walkPolynomial_eq_transfer f z b C₀ F.inputMatrix F.readState F.readInput h₀
  rw [φ] at hQ
  simp only [residual, map_one, one_smul, Q, hQ]
  rw [F.rationalTransfer_eq_resolvent]
  apply (rank_stateTransfer_sub_le z _ _ (F.inputMatrix.map f) (F.readState.map f)
    (F.readInput.map f) (rational_pencil_unit F.stateMatrix) (rational_pencil_unit C₀)).trans
  simpa only [Matrix.map_sub _ (map_sub f)] using rank_map_le f (F.stateMatrix - C₀)

/-- A nilpotent state matrix on `s` states admits a polynomial part of degree at most
`b` with remainder of rank at most `s / b`, for every positive truncation length `b`. -/
theorem nilpotent_compression [Fintype I] (hF : IsNilpotent F.stateMatrix) (b : ℕ) (hb : 0 < b) :
    ∃ Q : Matrix O I K[X], (∀ o i, (Q o i).natDegree ≤ b) ∧
      (F.residual 1 Q).rank * b ≤ s := by
  obtain ⟨C₀, h₀, hcut⟩ := exists_nilpotent_matrix_cut F.stateMatrix hF b hb
  obtain ⟨Q, hQ, hr⟩ := F.nilpotent_residual_split C₀ b h₀
  exact ⟨Q, hQ, (Nat.mul_le_mul_right _ hr).trans (by simpa using hcut)⟩

end
end Feedback

end FiniteFourier
end LinearAlgebra
end OAI

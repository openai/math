import OAI.LinearAlgebra.FiniteFourier.FeedbackCompression
import OAI.LinearAlgebra.FiniteFourier.InvariantCompression
import OAI.LinearAlgebra.FiniteFourier.CircuitNilpotent

/-! # State compression for binary feedback systems

For each positive block length the delayed transfer admits a normalized scalar
multiplier and a low-degree matrix polynomial, with a rank-bounded remainder
regular at both evaluation points.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix Polynomial
noncomputable section

variable {K I O : Type*} [Field K] [Fintype I] {s : ℕ}

/-- The reversed annihilator construction applied to a regular feedback system.
The chain cut gives the stronger remainder bound `b * rank R ≤ s`. -/
theorem Feedback.state_compression (F : Feedback K I O s) (hF : F.Regular) (b : ℕ) (hb : 0 < b) :
    ∃ (B : K[X]) (Q : Matrix O I K[X]), B.eval 1 = 1 ∧ B.natDegree ≤ 2 * b ∧
      (∀ o i, (Q o i).natDegree ≤ 2 * b) ∧ (F.residual B Q).rank * b ≤ s := by
  obtain ⟨C₀, g, hd, h₁, hg, hcut⟩ :=
    exists_compressed_state F.stateMatrix (isUnit_iff_ne_zero.mpr hF) b hb
  obtain ⟨B, Q, hB₁, hB, hQ, hR⟩ := F.general_residual_split_of_cut C₀ g hg h₁
  exact ⟨B, Q, hB₁, hB.trans hd, fun o i => (hQ o i).trans hd,
    (Nat.mul_le_mul_right b hR).trans (by simpa using hcut)⟩

/-- State compression in the form of Lemma `tr:compression`: a rational
identity with simultaneous regularity at zero and one and rank at most `2s/b`. -/
theorem Feedback.transfer_compression (F : Feedback K I O s) (hF : F.Regular)
    (b : ℕ) (hb : 0 < b) :
    ∃ (B : K[X]) (Q : Matrix O I K[X]) (R : Matrix O I (RatFunc K)),
      algebraMap K[X] (RatFunc K) B • F.rationalTransfer = Q.map (algebraMap K[X] (RatFunc K)) + R ∧
      B.eval 1 = 1 ∧ B.natDegree ≤ 2 * b ∧ (∀ o i, (Q o i).natDegree ≤ 2 * b) ∧
      R.rank * b ≤ 2 * s ∧
      (∀ o i, (R o i).denom.eval 0 ≠ 0) ∧ (∀ o i, (R o i).denom.eval 1 ≠ 0) := by
  obtain ⟨B, Q, hB₁, hB, hQ, hr⟩ := F.state_compression hF b hb
  refine ⟨B, Q, F.residual B Q, ?_, hB₁, hB, hQ, by omega, F.residual_regular_zero B Q,
    F.residual_regular_one B Q hF⟩
  unfold Feedback.residual
  abel

/-- For an acyclic binary circuit no scalar multiplier is needed, and the
polynomial degree drops to the block length. -/
theorem Circuit.transfer_compression (p : Circuit K I O s) (b : ℕ) (hb : 0 < b) :
    ∃ Q : Matrix O I K[X], (∀ o i, (Q o i).natDegree ≤ b) ∧
      (p.toFeedback.residual 1 Q).rank * b ≤ s :=
  p.toFeedback.nilpotent_compression p.stateMatrix_isNilpotent b hb

end

end FiniteFourier
end LinearAlgebra
end OAI

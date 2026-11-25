import OAI.LinearAlgebra.FiniteFourier.FeedbackBorder
import OAI.LinearAlgebra.FiniteFourier.CircuitReindex

/-! # Relabeling and scaling in the feedback model

Permuting the input and output labels and scaling their coordinates preserves
the bound on the number of feedback states.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

variable {K I O I' O' : Type*} [Field K] {s : ℕ}

private def scaledReindex (M : Matrix O I K) (eo : O ≃ O') (ei : I ≃ I')
    (b : O' → K) (a : I' → K) : Matrix O' I' K :=
  Matrix.of fun o i => b o * M (eo.symm o) (ei.symm i) * a i

namespace Feedback

private def gateSubst {W V : Type*} (g : BinaryGate K W) (e : W ≃ V) (a : V → K) :
    BinaryGate K V :=
  g.rewire fun w => (a (e w), e w)

private def readSubst {W V : Type*} (r : Readout K W) (e : W ≃ V) (a : V → K) (b : K) :
    Readout K V :=
  r.rewire b fun w => (a (e w), e w)

private theorem gateRow_subst {W V : Type*} (g : BinaryGate K W) (e : W ≃ V)
    (a : V → K) (v : V) : gateRow (gateSubst g e a) v = gateRow g (e.symm v) * a v := by
  classical
  obtain ⟨w,rfl⟩ := e.surjective v
  simp only [gateRow, gateSubst, BinaryGate.rewire, Pi.add_apply, Pi.single_apply, Equiv.symm_apply_apply,
    EmbeddingLike.apply_eq_iff_eq, add_mul]
  split_ifs <;> simp_all

private theorem readRow_subst {W V : Type*} (r : Readout K W) (e : W ≃ V)
    (a : V → K) (b : K) (v : V) :
    readRow (readSubst r e a b) v = b * readRow r (e.symm v) * a v := by
  classical
  obtain ⟨w,rfl⟩ := e.surjective v
  cases r with
  | zero => simp [readSubst, Readout.rewire, readRow]
  | scaled c z => by_cases h : w = z <;>
      simp [readSubst, Readout.rewire, readRow, h]

private def scaled (F : Feedback K I O s) (eo : O ≃ O') (ei : I ≃ I')
    (b : O' → K) (a : I' → K) : Feedback K I' O' s where
  equation j := gateSubst (F.equation j) (ei.sumCongr (Equiv.refl _)) (Sum.elim a fun _ => 1)
  output o := readSubst (F.output (eo.symm o)) (ei.sumCongr (Equiv.refl _)) (Sum.elim a fun _ => 1) (b o)

variable (F : Feedback K I O s) (eo : O ≃ O') (ei : I ≃ I') (b : O' → K) (a : I' → K)

private theorem state_scaled : (scaled F eo ei b a).stateMatrix = F.stateMatrix := by
  ext i j
  simp [stateMatrix, scaled, gateRow_subst]

private theorem matrix_scaled : (scaled F eo ei b a).matrix = scaledReindex F.matrix eo ei b a := by
  ext o i
  unfold matrix scaledReindex
  rw [state_scaled]
  simp only [Matrix.add_apply, Matrix.mul_apply, inputMatrix, readInput, readState,
    scaled, readRow_subst, gateRow_subst, Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.sumCongr_apply,
    Sum.map_inl, Sum.map_inr, Equiv.refl_apply, Sum.elim_inl, Sum.elim_inr, mul_one,
    Matrix.of_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

end Feedback

/-- Independent relabelings and coordinate scalings keep the exact feedback-state budget. -/
theorem FeedbackAtMost.scaledReindex {M : Matrix O I K} {S : ℕ} (h : FeedbackAtMost M S)
    (eo : O ≃ O') (ei : I ≃ I') (b : O' → K) (a : I' → K) :
    FeedbackAtMost (Matrix.of fun o i => b o * M (eo.symm o) (ei.symm i) * a i) S := by
  obtain ⟨s, hs, F, hf, rfl⟩ := h
  exact ⟨s, hs, F.scaled eo ei b a, by simpa [Feedback.Regular, Feedback.state_scaled] using hf,
    F.matrix_scaled eo ei b a⟩

end

end

end FiniteFourier
end LinearAlgebra
end OAI

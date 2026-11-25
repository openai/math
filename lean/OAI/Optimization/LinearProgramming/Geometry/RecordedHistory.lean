import OAI.Optimization.LinearProgramming.Contract.AppOracleMachine

/-! Consistency of the newest-first scalar history with the oracle used by the RAM. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open Contract RAM

/-- Every recorded answer is the oracle's answer at the preceding chronological history. -/
def answersMatch (o : ScalarOracle ℚ) : Contract.History ℚ → Prop
  | [] => True
  | (q,a)::h => a=o h q ∧ answersMatch o h

private theorem answersMatch_step {p : OracleProgram} {o : ScalarOracle ℚ}
    {s t : Config ℚ} {c : ℕ} (old : answersMatch o s.history)
    (h : oracleStep p o s=some (c,t)) : answersMatch o t.history := by
  obtain ⟨st,hist⟩ := s
  cases stop : st.output with
  | some tag => simp [oracleStep,stop] at h
  | none =>
    cases ins : p[st.pc]? with
    | none => simp [oracleStep,stop,ins] at h
    | some instruction =>
      cases instruction with
      | core i =>
        cases act : execInstr i st with
        | none => simp [oracleStep,stop,ins,act] at h
        | some z =>
          simp [oracleStep,stop,ins,act] at h
          obtain ⟨rfl,rfl⟩ := h
          exact old
      | query a b d e =>
        simp [oracleStep,stop,ins] at h
        obtain ⟨rfl,rfl⟩ := h
        exact ⟨rfl,old⟩

theorem answersMatch_run {p : OracleProgram} {o : ScalarOracle ℚ} {s t : Config ℚ} {c : ℕ}
    (h : OracleRun p o s c t) (old : answersMatch o s.history) : answersMatch o t.history := by
  induction h with
  | refl => exact old
  | next edge rest ih => exact ih (answersMatch_step old edge)

theorem answersMatch_suffix (o : ScalarOracle ℚ) (front tail : Contract.History ℚ)
    (h : answersMatch o (front++tail)) : answersMatch o tail := by
  induction front with
  | nil => exact h
  | cons e es ih =>
    obtain ⟨q,a⟩ := e
    exact ih h.2

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI

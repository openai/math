import OAI.LinearAlgebra.FiniteFourier.ProgramEquations
import OAI.LinearAlgebra.FiniteFourier.FeedbackBorder

/-! # Acyclic circuits as uniquely solvable feedback systems

Each gate supplies its own equation. Evaluating gates in order gives the unique
state vector. The same readouts therefore realize exactly the circuit matrix.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {K I O : Type*} [Field K] {s : ℕ}

/-- Regard each gate of the program as one simultaneous state equation. -/
def Circuit.toFeedback (p : Circuit K I O s) : Feedback K I O s where
  equation := p.program.equations
  output := p.output

variable [Fintype I]

theorem Circuit.toFeedback_isState_iff (p : Circuit K I O s) (x : I → K) (v : Fin s → K) :
    p.toFeedback.IsState x v ↔ v = p.program.value x := by
  rw [Feedback.isState_iff_wire_equations]
  exact p.program.solves_equations_iff x v

theorem Circuit.toFeedback_regular (p : Circuit K I O s) : p.toFeedback.Regular := by
  rw [Feedback.regular_iff_existsUnique_state]
  intro x
  exact ⟨p.program.value x, (p.toFeedback_isState_iff x _).2 rfl,
    fun v hv => (p.toFeedback_isState_iff x v).1 hv⟩

/-- At every input, the unique solution of the feedback equations gives the values
stored by the acyclic program. -/
theorem Circuit.toFeedback_state (p : Circuit K I O s) (x : I → K) :
    p.toFeedback.state x = p.program.value x :=
  (p.toFeedback_isState_iff x _).1 <|
    (p.toFeedback.isState_iff_eq_state p.toFeedback_regular x _).2 rfl

theorem Circuit.toFeedback_mulVec (p : Circuit K I O s) (x : I → K) :
    p.toFeedback.matrix *ᵥ x = p.eval x := by
  ext o
  rw [Feedback.matrix_mulVec_apply, p.toFeedback_state]
  change (match p.output o with
    | .zero => 0
    | .scaled a w => a * Sum.elim x (p.program.value x) w) = (p.output o).eval _
  cases p.output o <;> rfl

/-- The embedding introduces no extra states, and gives the same transfer matrix. -/
theorem Circuit.toFeedback_realizes (p : Circuit K I O s) :
    p.toFeedback.Realizes p.matrix := by
  classical
  refine ⟨p.toFeedback_regular, ?_⟩
  ext o i
  have h := congrFun (p.toFeedback_mulVec (Pi.single i 1)) o
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Circuit.matrix] using h

theorem RealizableAtMost.feedback {M : Matrix O I K} (h : RealizableAtMost M s) :
    FeedbackAtMost M s := by
  obtain ⟨r, hr, p, rfl⟩ := h
  exact ⟨r, hr, p.toFeedback, p.toFeedback_realizes⟩

theorem RealizableAtMost.geometricBorder {M : Matrix O I K} (h : RealizableAtMost M s) :
    GeometricBorderAtMost M s :=
  h.feedback.geometricBorder

end FiniteFourier
end LinearAlgebra
end OAI

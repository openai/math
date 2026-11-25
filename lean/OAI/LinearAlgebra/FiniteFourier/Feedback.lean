import OAI.LinearAlgebra.FiniteFourier.Circuit
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Binary feedback systems

Each state reads two wires from the disjoint union of the inputs and all states.
Repeated wires and zero coefficients are allowed. The inverse matrix formula
agrees with the unique solution of the simultaneous scalar equations.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix
noncomputable section

/-- A binary linear system with feedback, with inputs indexed by `I`, outputs
indexed by `O` and `s` simultaneous state equations. -/
structure Feedback (K I O : Type*) (s : ℕ) where
  equation : Fin s → BinaryGate K (I ⊕ Fin s)
  output : O → Readout K (I ⊕ Fin s)

namespace Feedback

variable {K I O : Type*} [Field K] {s : ℕ}

/-- The coefficient row of a binary equation, adding the coefficients when
both incoming wires have the same source. -/
def gateRow {W : Type*} (g : BinaryGate K W) : W → K := by
  classical
  exact Pi.single g.left g.leftCoeff + Pi.single g.right g.rightCoeff

theorem gateRow_dotProduct {W : Type*} [Fintype W] (g : BinaryGate K W) (v : W → K) :
    gateRow g ⬝ᵥ v = g.leftCoeff * v g.left + g.rightCoeff * v g.right := by
  classical
  simp [gateRow, add_dotProduct, single_dotProduct]

/-- Zero or one weighted source at an output. -/
def readRow {W : Type*} (g : Readout K W) : W → K := by
  classical
  exact g.casesOn 0 (fun c w => Pi.single w c)

variable (F : Feedback K I O s)

/-- The coefficient of state `j` in the equation for state `i`. -/
def stateMatrix : Matrix (Fin s) (Fin s) K := fun i j => gateRow (F.equation i) (.inr j)

/-- The coefficient of input `j` in the equation for state `i`. -/
def inputMatrix : Matrix (Fin s) I K := fun i j => gateRow (F.equation i) (.inl j)

/-- State-to-output readout. -/
def readState : Matrix O (Fin s) K := fun o j => readRow (F.output o) (.inr j)

/-- Direct input-to-output readout. -/
def readInput : Matrix O I K := fun o j => readRow (F.output o) (.inl j)

/-- Unique solvability in determinant form. -/
def Regular : Prop := (1 - F.stateMatrix).det ≠ 0

/-- The input-output matrix at delay one. Its circuit semantics is used on
regular systems. -/
def matrix : Matrix O I K :=
  F.readInput + F.readState * (1 - F.stateMatrix)⁻¹ * F.inputMatrix

/-- Realizability by this particular regular feedback system. -/
def Realizes (M : Matrix O I K) : Prop := F.Regular ∧ F.matrix = M

variable [Fintype I]

/-- The state equation for an input `x` and a candidate state vector `v`. -/
def IsState (x : I → K) (v : Fin s → K) : Prop :=
  v = F.stateMatrix *ᵥ v + F.inputMatrix *ᵥ x

theorem isState_iff (x : I → K) (v : Fin s → K) :
    F.IsState x v ↔ (1 - F.stateMatrix) *ᵥ v = F.inputMatrix *ᵥ x := by
  rw [IsState, sub_mulVec, one_mulVec, sub_eq_iff_eq_add']

/-- The solution of the feedback equations at a regular point. -/
def state (x : I → K) : Fin s → K :=
  (1 - F.stateMatrix)⁻¹ *ᵥ (F.inputMatrix *ᵥ x)

theorem isState_iff_eq_state (h : F.Regular) (x : I → K) (v : Fin s → K) :
    F.IsState x v ↔ v = F.state x := by
  have hu : IsUnit (1 - F.stateMatrix).det := isUnit_iff_ne_zero.mpr h
  rw [F.isState_iff]
  constructor
  · intro hv
    rw [state, ← hv, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  · rintro rfl
    rw [state, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]

/-- Regularity is equivalent to unique solvability for every input,
including when there are no states or no inputs. -/
theorem regular_iff_existsUnique_state :
    F.Regular ↔ ∀ x, ∃! v, F.IsState x v := by
  constructor
  · intro h x
    exact ⟨F.state x, (F.isState_iff_eq_state h x _).2 rfl,
      fun v hv => (F.isState_iff_eq_state h x v).1 hv⟩
  · intro h
    obtain ⟨v, _, hv⟩ := h 0
    have hzero : F.IsState 0 0 := by simp [IsState]
    apply IsUnit.ne_zero
    apply (isUnit_iff_isUnit_det _).mp
    apply mulVec_injective_iff_isUnit.mp
    intro a b hab
    apply sub_eq_zero.mp
    have hz : F.IsState 0 (a - b) :=
      (F.isState_iff _ _).2 (by simp [mulVec_sub, hab])
    exact (hv _ hz).trans (hv _ hzero).symm

/-- The matrix readout agrees with the weighted wires selected by the outputs. -/
theorem matrix_mulVec (x : I → K) :
    F.matrix *ᵥ x = F.readInput *ᵥ x + F.readState *ᵥ F.state x := by
  simp only [matrix, state, add_mulVec, ← mulVec_mulVec]

private theorem splitWireRow (r : I ⊕ Fin s → K) (x : I → K) (v : Fin s → K) :
    r ⬝ᵥ Sum.elim x v = (fun j => r (.inl j)) ⬝ᵥ x + (fun j => r (.inr j)) ⬝ᵥ v := by
  simp [dotProduct, Fintype.sum_sum_type]

/-- Matrix semantics agrees with the two scalar reads in each equation. -/
theorem isState_iff_wire_equations (x : I → K) (v : Fin s → K) :
    F.IsState x v ↔ ∀ i, v i =
      (F.equation i).leftCoeff * Sum.elim x v (F.equation i).left +
      (F.equation i).rightCoeff * Sum.elim x v (F.equation i).right := by
  classical
  rw [IsState, funext_iff]
  refine forall_congr' fun i => ?_
  change (v i = (fun j => gateRow (F.equation i) (.inr j)) ⬝ᵥ v +
    (fun j => gateRow (F.equation i) (.inl j)) ⬝ᵥ x) ↔ _
  rw [add_comm, ← splitWireRow, gateRow_dotProduct]

/-- The selected scaled wire evaluates to the corresponding row of the
realized matrix on the input. -/
theorem matrix_mulVec_apply (x : I → K) (o : O) :
    (F.matrix *ᵥ x) o = match F.output o with
      | .zero => 0
      | .scaled a w => a * Sum.elim x (F.state x) w := by
  rw [F.matrix_mulVec]
  change (fun j => readRow (F.output o) (.inl j)) ⬝ᵥ x +
      (fun j => readRow (F.output o) (.inr j)) ⬝ᵥ F.state x = _
  rw [← splitWireRow]
  cases F.output o <;> simp [readRow, single_dotProduct]

end Feedback
end

end FiniteFourier
end LinearAlgebra
end OAI

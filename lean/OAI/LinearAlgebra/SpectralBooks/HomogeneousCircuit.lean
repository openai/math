import OAI.LinearAlgebra.SpectralBooks.FormalBlockFamily
import OAI.LinearAlgebra.SpectralBooks.ParseSpan

/-! # Extracting homogeneous components with shared registers

At every gate the circuit retains one register per degree through `D`.
The Cauchy product at a multiplication gate costs at most `2*(D+1)^2`
operations for all its components together.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic Arithmetic.RecursiveBlock MvPolynomial

noncomputable section

variable {F σ : Type*} [Field F]

private abbrev ComponentState (σ : Type*) (r D : ℕ) := σ ⊕ Fin r × Fin (D + 1)

private def componentGate {r D : ℕ} (g : Gate F σ (Fin r)) (k : Fin (D+1)) :
    Expression F (ComponentState σ r D) :=
  match g with
  | .constant c => .constant (if k.val = 0 then c else 0)
  | .input i => if k.val = 1 then .input (.inl i) else .constant 0
  | .add i j => .add (.input (.inr (i,k))) (.input (.inr (j,k)))
  | .sub i j => .sub (.input (.inr (i,k))) (.input (.inr (j,k)))
  | .mul i j => LinearExpression.sumFin (k.val+1) fun t =>
      .mul (.input (.inr (i, ⟨t.val, by omega⟩)))
        (.input (.inr (j, ⟨k.val-t.val, by omega⟩)))

private def componentStep {r D : ℕ} (g : Gate F σ (Fin r)) :
    ComponentState σ (r+1) D → Expression F (ComponentState σ r D)
  | .inl i => .input (.inl i)
  | .inr (i,k) => Fin.cases (componentGate g k) (fun j => .input (.inr (j,k))) i

private def statePolynomial {r D : ℕ} (p : Program F σ r) :
    ComponentState σ r D → MvPolynomial σ F
  | .inl i => X i
  | .inr (i,k) => homogeneousComponent k.val (registerPolynomial p i)

private theorem poly_sumFin {I : Type*} (n : ℕ) (f : Fin n → Expression F I) :
    expressionPolynomial (LinearExpression.sumFin n f) = ∑ t, expressionPolynomial (f t) := by
  induction n with
  | zero => simp [LinearExpression.sumFin, expressionPolynomial]
  | succ n ih => simp only [LinearExpression.sumFin, expressionPolynomial, ih, Fin.sum_univ_succ]

private theorem componentGate_correct {r D : ℕ} (p : Program F σ r)
    (g : Gate F σ (Fin r)) (k : Fin (D+1)) :
    bind₁ (statePolynomial p) (expressionPolynomial (componentGate g k)) =
      homogeneousComponent k.val (gatePolynomial g (registerPolynomial p)) := by
  cases g with
  | constant c =>
    by_cases hk : k.val = 0 <;> simp [componentGate, expressionPolynomial, gatePolynomial,
      homogeneousComponent_of_mem (isHomogeneous_C σ c), hk]
  | input i =>
    by_cases hk : k.val = 1 <;> simp [componentGate, expressionPolynomial, gatePolynomial,
      homogeneousComponent_of_mem (isHomogeneous_X F i), hk, statePolynomial]
  | add i j => simp [componentGate, expressionPolynomial, gatePolynomial, statePolynomial]
  | sub i j => simp [componentGate, expressionPolynomial, gatePolynomial, statePolynomial]
  | mul i j =>
    simp only [componentGate, poly_sumFin, map_sum, expressionPolynomial, map_mul, bind₁_X_right,
      statePolynomial, gatePolynomial, homogeneousComponent_product]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]

private theorem componentGate_cost {r D : ℕ} (g : Gate F σ (Fin r)) (k : Fin (D+1)) :
    (componentGate g k).cost ≤ 2*(D+1)*g.cost := by
  cases g with
  | constant c => simp [componentGate, Expression.cost, Gate.cost]
  | input i =>
    by_cases hk : k.val = 1 <;> simp [componentGate, Expression.cost, Gate.cost, hk]
  | add i j => simp [componentGate, Expression.cost, Gate.cost]; omega
  | sub i j => simp [componentGate, Expression.cost, Gate.cost]; omega
  | mul i j =>
    simp [componentGate, LinearExpression.cost_sumFin, Expression.cost, Gate.cost]
    omega

private theorem componentStep_cost [Fintype σ] {r D : ℕ} (g : Gate F σ (Fin r)) :
    (Family.expressions (@componentStep F σ _ r D g)).cost ≤ 2*(D+1)^2*g.cost := by
  classical
  rw [Family.cost_expressions, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [componentStep, Expression.cost, Finset.sum_const_zero, zero_add, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ, add_zero]
  rw [← Fin.sum_univ_succ (fun k : Fin (D+1) => (componentGate g k).cost)]
  calc
    _ ≤ ∑ _k : Fin (D+1), 2*(D+1)*g.cost := Finset.sum_le_sum fun k _ => componentGate_cost g k
    _ = 2*(D+1)^2*g.cost := by simp; ring

/-- One division-free program computes all homogeneous components through the
cutoff at all registers of the original program, charging the old gates once. -/
theorem exists_homogeneousComponent_program [Fintype σ] (D : ℕ) {r : ℕ}
    (p : Program F σ r) :
    ∃ (s : ℕ) (q : Program F σ s) (out : Fin r → Fin (D+1) → Fin s),
      (∀ i k, registerPolynomial q (out i k) =
        homogeneousComponent k.val (registerPolynomial p i)) ∧
      q.cost ≤ 2*(D+1)^2*p.cost := by
  classical
  suffices ∃ q : Family F σ (ComponentState σ r D),
      (∀ i, familyPolynomial q i = statePolynomial p i) ∧ q.cost ≤ 2*(D+1)^2*p.cost by
    obtain ⟨q, hq, hc⟩ := this
    exact ⟨q.registers, q.program, fun i k => q.output (.inr (i,k)),
      fun i k => hq (.inr (i,k)), hc⟩
  induction p with
  | nil =>
    let e : ComponentState σ 0 D → Expression F σ := Sum.elim Expression.input (fun j => j.1.elim0)
    refine ⟨Family.expressions e, ?_, ?_⟩
    · rintro (i|⟨i,k⟩)
      · exact familyPolynomial_expressions e (.inl i)
      · exact i.elim0
    · simp [Family.cost_expressions, e, Fintype.sum_sum_type, Expression.cost, Program.cost]
  | @step r p g ih =>
    obtain ⟨q, hq, hc⟩ := ih
    refine ⟨q.compose (Family.expressions (componentStep g)), ?_, ?_⟩
    · intro i
      rw [familyPolynomial_compose, familyPolynomial_expressions, funext hq]
      rcases i with i | ⟨i,k⟩
      · simp [componentStep, expressionPolynomial, statePolynomial]
      · refine Fin.cases ?_ (fun j => ?_) i
        · exact componentGate_correct p g k
        · simp [componentStep, expressionPolynomial, statePolynomial]
    · rw [Family.cost_compose, Program.cost_step, Nat.mul_add]
      exact Nat.add_le_add hc (componentStep_cost g)

end

end SpectralBooks
end LinearAlgebra
end OAI

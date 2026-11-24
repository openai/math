import OAI.Computability.VPVNP.EvaluatorMatrixStep
import OAI.Computability.VPVNP.EvaluatorDigitSchedule

/-!
# Counting a streamed sequence of linear steps

After an index guess, the evaluator retains only that index and its running
product. Different branches may take different times to query their matrix
entries. A common bound per step suffices for the modular count: after every
permitted choice the remaining clock still covers the remaining steps.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator

open RAMTape

variable {P : Type*} {Op : Type*}

/-- The continuation count as a function of the remaining instruction budget and the current
evaluator stack bank. -/
abbrev Continuation (P : Type*) := ℕ → Stacks P → ℕ

/-- Continuation semantics of the chronological actions, independently of the
finite control that emits the schedule. -/
def actionCount (step : Op → Continuation P → Continuation P) (finish : Continuation P) :
    List Op → Continuation P
  | [] => finish
  | op :: ops => step op (actionCount step finish ops)

variable {p n : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Algebra (ZMod p) K]
    (matrix : Op → Matrix (Fin n) (Fin n) K) (coord : K →ₗ[ZMod p] ZMod p)
    (unit : Fin n) (bank : Fin n → K → Stacks P)
    (step : Op → Continuation P → Continuation P) (finish : Continuation P)
    (stepBound finishBound : ℕ)
    (hstep : ∀ op i a fuel, stepBound ≤ fuel → ∃ delay : Fin n → ℕ,
      (∀ j, delay j ≤ stepBound) ∧ ∀ c,
        step op c fuel (bank i a) =
          ∑ j, c (fuel - delay j) (bank j (a * matrix op i j)))
    (hfinish : ∀ i a fuel, finishBound ≤ fuel →
      (finish fuel (bank i a) : ZMod p) = coord (if i = unit then a else 0))

include hstep hfinish in
/-- After all streamed queries, reducing the integer count modulo the prime
gives the first coordinate of the accumulated weighted matrix product. -/
theorem actionCount_mod (ops : List Op) (i : Fin n) (a : K) (fuel : ℕ)
    (ht : ops.length * stepBound + finishBound ≤ fuel) :
    (actionCount step finish ops fuel (bank i a) : ZMod p) =
      coord (a * (ops.map matrix).prod i unit) := by
  induction ops generalizing fuel i a with
  | nil =>
    have he := hfinish i a fuel (by simpa using ht)
    by_cases hi : i = unit <;> simpa [actionCount, Matrix.one_apply, hi] using he
  | cons op ops ih =>
    have ht' : ops.length * stepBound + stepBound + finishBound ≤ fuel := by
      simpa only [List.length_cons, Nat.succ_mul] using ht
    obtain ⟨delay, hd, he⟩ := hstep op i a fuel (by omega)
    simp only [actionCount, he, Nat.cast_sum, List.map_cons, List.prod_cons, Matrix.mul_apply]
    rw [Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    have h := ih j (a * matrix op i j) (fuel - delay j) (by have := hd j; omega)
    simpa only [mul_assoc] using h

/-- Apply the chronological count identity to the actual Frobenius and label
matrices in their monomial basis. The functional is applied after all digits. -/
theorem monomial_actionCount_mod [Fintype K] {A : Type*} [CommRing A] [Algebra K A]
    [Algebra (ZMod p) A] [IsScalarTower (ZMod p) K A] {t : ℕ}
    (X : Fin t → A) (b : Module.Basis (Fin n) K A) (hb : b unit = 1)
    (programStep : EvaluatorDigitSchedule.Action t → Continuation P → Continuation P)
    (hs : ∀ op i a fuel, stepBound ≤ fuel → ∃ delay : Fin n → ℕ,
      (∀ j, delay j ≤ stepBound) ∧ ∀ c, programStep op c fuel (bank i a) =
        ∑ j, c (fuel - delay j) (bank j (a *
          (LinearMap.toMatrixAlgEquiv b (EvaluatorDigitSchedule.actionMap K X op)) j i)))
    (width : ℕ) (e : Fin t → ℕ) (he : ∀ i, e i < 2 ^ width) (fuel : ℕ)
    (hclock : width * (1 + t * (Fintype.card K - 1)) * stepBound + finishBound ≤ fuel)
    (finalCount : ∀ i a fuel, finishBound ≤ fuel →
      (finish fuel (bank i a) : ZMod p) = coord (if i = unit then a else 0)) :
    (actionCount programStep finish
        ((EvaluatorDigitSchedule.columns (Fintype.card K) width e).flatMap EvaluatorDigitSchedule.emit)
        fuel (bank unit 1) : ZMod p) = primeFunctional b unit coord (∏ i, X i ^ e i) := by
  let ops := (EvaluatorDigitSchedule.columns (Fintype.card K) width e).flatMap EvaluatorDigitSchedule.emit
  let m (op : EvaluatorDigitSchedule.Action t) :=
    (LinearMap.toMatrixAlgEquiv b (EvaluatorDigitSchedule.actionMap K X op)).transpose
  have ht : ops.length * stepBound + finishBound ≤ fuel :=
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (EvaluatorDigitSchedule.action_count_le K width e)) _).trans hclock
  have h := actionCount_mod m coord unit bank programStep finish stepBound finishBound hs finalCount ops unit 1 fuel ht
  have hmaps : ops.map m = transitionMatrices b (digitProgram K X width e) := by
    rw [transitionMatrices, ← EvaluatorDigitSchedule.actions_eq_digitProgram K X, List.map_map]
    rfl
  rw [hmaps, one_mul, transitionMatrices_unit_entry b unit hb, digitProgram_eval K X width e he] at h
  exact h

end Evaluator

end VPVNP
end Computability
end OAI

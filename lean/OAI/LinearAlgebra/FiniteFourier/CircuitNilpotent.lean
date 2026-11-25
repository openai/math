import OAI.LinearAlgebra.FiniteFourier.CircuitToFeedback

/-! # Nilpotence of the delayed state matrix of an acyclic circuit -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {K I O : Type*} [Field K] {s : ℕ}

private def earlierWire (j : Fin s) : I ⊕ Fin s → Prop :=
  Sum.elim (fun _ => True) (fun i => j < i)

private theorem earlierWire_zero (w : I ⊕ Fin s) :
    earlierWire 0 (Sum.map id Fin.succ w) := by
  cases w <;> simp [earlierWire]

private theorem earlierWire_succ (j : Fin s) (w : I ⊕ Fin s) :
    earlierWire j.succ (Sum.map id Fin.succ w) ↔ earlierWire j w := by
  cases w <;> simp [earlierWire]

omit [Field K] in
private theorem earlier_sources (p : Program K I s) (j : Fin s) :
    earlierWire j (p.equations j).left ∧ earlierWire j (p.equations j).right := by
  induction p with
  | nil => exact j.elim0
  | step p g ih =>
    refine Fin.cases ?_ (fun t => ?_) j
    · exact ⟨earlierWire_zero g.left, earlierWire_zero g.right⟩
    · exact ⟨(earlierWire_succ _ _).mpr (ih t).1, (earlierWire_succ _ _).mpr (ih t).2⟩

/-- State rows reference only earlier gates, which have larger register indices. -/
theorem Circuit.stateMatrix_eq_zero_of_le (p : Circuit K I O s) {a b : Fin s} (h : b ≤ a) :
    p.toFeedback.stateMatrix a b = 0 := by
  classical
  have hp := earlier_sources p.program a
  have hn (w : I ⊕ Fin s) (hw : earlierWire a w) : Sum.inr b ≠ w := by
    rintro rfl
    exact (not_lt_of_ge h) hw
  simp [Feedback.stateMatrix, Feedback.gateRow, Circuit.toFeedback,
    hn _ hp.1, hn _ hp.2]

/-- Each state-to-state step strictly increases the index. A coefficient of a
power can survive only if the column exceeds the row by at least the exponent. -/
theorem Circuit.stateMatrix_pow_eq_zero_of_lt (p : Circuit K I O s) (n : ℕ)
    (a b : Fin s) (h : (b : ℕ) < (a : ℕ) + n) : (p.toFeedback.stateMatrix ^ n) a b = 0 := by
  induction n generalizing a b with
  | zero =>
    have hab : a ≠ b := by intro e; subst b; omega
    simp [hab]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : (k : ℕ) < (a : ℕ) + n
    · rw [ih a k hk, zero_mul]
    · rw [p.stateMatrix_eq_zero_of_le (show b ≤ k by change (b : ℕ) ≤ k; omega), mul_zero]

/-- The state matrix of a circuit on `s` gates is killed by its `s`-th power. -/
theorem Circuit.stateMatrix_pow_size (p : Circuit K I O s) : p.toFeedback.stateMatrix ^ s = 0 := by
  ext a b
  exact p.stateMatrix_pow_eq_zero_of_lt _ _ _ (by have := b.isLt; omega)

theorem Circuit.stateMatrix_isNilpotent (p : Circuit K I O s) :
    IsNilpotent p.toFeedback.stateMatrix := ⟨s, p.stateMatrix_pow_size⟩

end FiniteFourier
end LinearAlgebra
end OAI

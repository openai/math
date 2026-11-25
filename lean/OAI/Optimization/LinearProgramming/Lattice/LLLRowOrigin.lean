import OAI.Optimization.LinearProgramming.Lattice.LLLReachNative

/-! Provenance of every stored basis row during the classical LLL pass loop. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open Hex.Internal

private theorem foldr_preserves_value {α β : Type} {k : ℕ} (value : α → β)
    (f : Fin k → α → α) (hf : ∀ i s, value (f i s) = value s) (s : α) :
    value (Fin.foldr k f s) = value s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.foldr_succ, hf]
    exact ih _ (fun i => hf i.succ)

/-- A pass modifies only the row at its cursor; earlier and later rows are literally preserved. -/
theorem native_sizeReduce_row_other {n m : ℕ} (s : LLLState n m) (k i : Fin n) (hi : i ≠ k) :
    (s.sizeReduce k.val).b.row i = s.b.row i := by
  unfold LLLState.sizeReduce
  rw [dite_eq_left k.isLt]
  apply foldr_preserves_value (fun t : LLLState n m => t.b.row i)
  intro j a
  unfold LLLState.sizeReduceColumn
  dsimp only
  split
  · exact Hex.Matrix.row_rowAdd_of_ne _ _ _ hi
  · rfl

private theorem swapStep_row_from_input {n m : ℕ} (s : LLLState n m) (k : Fin n)
    (hk : 0 < k.val) (i : Fin n) : ∃ j, (s.swapStep k.val).b.row i = s.b.row j := by
  let l := Hex.GramSchmidt.prevRow k hk
  have hb : (s.swapStep k.val).b = Hex.Matrix.rowSwap s.b l k := by
    unfold LLLState.swapStep
    rw [dite_eq_left k.isLt, dite_eq_left hk]
    rfl
  rw [hb]
  by_cases hl : i = l
  · subst i
    exact ⟨k, Hex.Matrix.row_rowSwap_left ..⟩
  by_cases hi : i = k
  · subst i
    exact ⟨l, Hex.Matrix.row_rowSwap_right ..⟩
  exact ⟨i, Hex.Matrix.row_rowSwap_of_ne _ hl hi⟩

private theorem next_row_after_sizeReduce {n m : ℕ} (c d : ReductionCursor n m)
    (hn : c.next = some d) :
    ∃ _hk : c.index < n, ∀ i : Fin n, ∃ j : Fin n,
      d.state.b.row i = (c.state.sizeReduce c.index).b.row j := by
  unfold ReductionCursor.next at hn
  split at hn <;> rename_i hk
  · refine ⟨hk, ?_⟩
    dsimp only at hn
    split at hn
    · cases hn
      exact fun i => ⟨i, rfl⟩
    · cases hn
      exact swapStep_row_from_input _ ⟨c.index,hk⟩ c.positive
  · simp at hn

/-- Every row at a later cursor is either an original row or the target row of a
completed size-reduction pass on the path to that cursor. The equality is in the
full integer row, including its order and signs. -/
theorem nativeReach_row_origin {n m : ℕ} {c d : ReductionCursor n m} (h : c.Reaches d)
    (i : Fin n) :
    (∃ j, d.state.b.row i = c.state.b.row j) ∨
    ∃ a : ReductionCursor n m, c.Reaches a ∧ a.Reaches d ∧
      ∃ hk : a.index < n,
        d.state.b.row i = (a.state.sizeReduce a.index).b.row ⟨a.index, hk⟩ := by
  induction h generalizing i with
  | refl => exact Or.inl ⟨i, rfl⟩
  | @step a b hca hab ih =>
    obtain ⟨hk, hm⟩ := next_row_after_sizeReduce a b hab
    obtain ⟨j, he⟩ := hm i
    by_cases hj : j = ⟨a.index, hk⟩
    · exact Or.inr ⟨a, hca, (ReductionCursor.Reaches.refl (c := a)).step hab,
        hk, he.trans (congrArg _ hj)⟩
    · have he' := he.trans (native_sizeReduce_row_other a.state ⟨a.index,hk⟩ j hj)
      rcases ih j with ⟨j', hj'⟩ | ⟨a', hca', ha'a, hk', hj'⟩
      · exact Or.inl ⟨j', he'.trans hj'⟩
      · exact Or.inr ⟨a', hca', ha'a.step hab, hk', he'.trans hj'⟩

end Lattice
end LinearProgramming
end Optimization
end OAI

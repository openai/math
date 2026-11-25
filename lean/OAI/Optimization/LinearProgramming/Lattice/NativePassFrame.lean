import OAI.Optimization.LinearProgramming.Lattice.LLLColumnTrace
import OAI.Optimization.LinearProgramming.Lattice.NativeColumnValidity

/-! Invariants over all binary-controller states of one native size-reduction pass,
including both its incoming and its final state. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open Hex.Internal

/-- One of the states serialized by the descending inner-loop controller. -/
def IsPassState {n m : ℕ} (s : LLLState n m) (k : Fin n) (t : LLLState n m) : Prop :=
  t = (sizeReduceColumnTrace s k).1 ∨ ∃ j, (j,t) ∈ (sizeReduceColumnTrace s k).2

theorem passState_invariant {n m : ℕ} {s t : LLLState n m} {k : Fin n}
    (ht : IsPassState s k t) (P : ℕ → LLLState n m → Prop) (h0 : P 0 s)
    (hstep : ∀ a u j (hj : j < k), P a u → P (a+1) (u.sizeReduceColumn j k hj)) :
    ∃ a ≤ k.val, P a t := by
  have h := columnTraceFrom_invariant k P hstep k.val le_rfl s 0 h0
  rcases ht with rfl | ⟨j,hj⟩
  · exact ⟨0+k.val, by omega, h.1⟩
  · obtain ⟨_,ha⟩ := h.2 (j,t) hj
    exact ⟨0+(k.val-1-j.val), by omega, ha⟩

theorem native_pass_frame {n m : ℕ} {s t : LLLState n m} {k : Fin n}
    (ht : IsPassState s k t) (hv : s.Valid) (hi : s.b.independent) :
    t.Valid ∧ t.b.independent ∧ t.d = s.d ∧
      ∀ i j : Fin n, i ≤ j → (t.ν.getRow i).get j = (s.ν.getRow i).get j := by
  let P (_ : ℕ) (u : LLLState n m) := u.Valid ∧ u.b.independent ∧ u.d = s.d ∧
    ∀ i j : Fin n, i ≤ j → (u.ν.getRow i).get j = (s.ν.getRow i).get j
  apply (passState_invariant ht P ⟨hv, hi, rfl, fun _ _ _ => rfl⟩ ?_).choose_spec.2
  intro _ u j hj hu
  exact ⟨LLLState.sizeReduceColumn_valid u j k hj hu.1,
    native_column_independent u j k hj hu.2.1,
    (native_column_gram_table u j k hj).trans hu.2.2.1,
    fun i l hil => (native_column_upper_frame u j k hj i l hil).trans (hu.2.2.2 i l hil)⟩

/-- The entire pass preserves the unused triangle, including the diagonal. -/
theorem native_sizeReduce_upper_frame {n m : ℕ} (s : LLLState n m) (k i j : Fin n)
    (hij : i ≤ j) :
    ((s.sizeReduce k.val).ν.getRow i).get j = (s.ν.getRow i).get j := by
  let P (_ : ℕ) (t : LLLState n m) := (t.ν.getRow i).get j = (s.ν.getRow i).get j
  rw [← sizeReduceColumnTrace_result s k]
  have h : IsPassState s k (sizeReduceColumnTrace s k).1 := Or.inl rfl
  obtain ⟨_,_,hp⟩ := passState_invariant h P rfl
    (fun _ u l hl hu => (native_column_upper_frame u l k hl i j hij).trans hu)
  exact hp

end Lattice
end LinearProgramming
end Optimization
end OAI

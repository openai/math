module

public import HexLLL.Native
import all HexLLLMathlib.ReductionInvariant

/-! State properties used to bound intermediate native size-reduction columns.
The column-reduction lemmas are from Kim Morrison's
[Hex LLL reduction invariants](https://github.com/leanprover/hex-lll-theory/blob/761108380d7bdae23181785d52703b4883388da1/HexLLLMathlib/ReductionInvariant.lean)
(© 2026 Lean FRO, LLC, Apache-2.0). -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open Hex.Internal

public theorem native_column_independent {n m : ℕ} (s : LLLState n m)
    (j k : Fin n) (hj : j < k) (hi : s.b.independent) :
    (s.sizeReduceColumn j k hj).b.independent :=
  LLLState.sizeReduceColumn_independent s j k hj hi

public theorem native_column_gram_table {n m : ℕ} (s : LLLState n m)
    (j k : Fin n) (hj : j < k) : (s.sizeReduceColumn j k hj).d = s.d :=
  LLLState.sizeReduceColumn_d_eq s j k hj

public theorem native_column_basis {n m : ℕ} (s : LLLState n m)
    (j k : Fin n) (hj : j < k) :
    (s.sizeReduceColumn j k hj).b =
      if 2 * ((s.ν.getRow k).get j).natAbs > s.d.get j.succ then
        Hex.GramSchmidt.Int.sizeReduce s.b j k
          (LLLState.nearestQuotient ((s.ν.getRow k).get j) (s.d.get j.succ))
      else s.b := by
  by_cases h : 2 * ((s.ν.getRow k).get j).natAbs > s.d.get j.succ
  · rw [ite_eq_left h]
    exact LLLState.sizeReduceColumn_b_reduce s j k hj h
  · rw [ite_eq_right h]
    have hh : ¬ 2 * ((s.ν.getRow k).get j).natAbs >
      s.d.get ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩ := h
    simp [LLLState.sizeReduceColumn, hh]

/-- Updating a strict lower-triangular coefficient does not touch any upper-triangle cell. -/
public theorem native_column_upper_frame {n m : ℕ} (s : LLLState n m)
    (j k : Fin n) (hj : j < k) (i l : Fin n) (hil : i ≤ l) :
    ((s.sizeReduceColumn j k hj).ν.getRow i).get l = (s.ν.getRow i).get l := by
  by_cases hi : i = k
  · subst i
    exact LLLState.sizeReduceColumn_ν_get_above_pivot s j k hj l (lt_of_lt_of_le hj hil)
  · by_cases h : 2 * ((s.ν.getRow k).get j).natAbs > s.d.get j.succ
    · rw [LLLState.sizeReduceColumn_ν_get_ne s j k hj h i hi]
    · have hh : ¬ 2 * ((s.ν.getRow k).get j).natAbs >
        s.d.get ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩ := h
      simp [LLLState.sizeReduceColumn, hh]

end Lattice
end LinearProgramming
end Optimization
end OAI

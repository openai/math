import OAI.Optimization.LinearProgramming.Lattice.BitState
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! Direct bounds on the framed binary encoding, including arbitrary ragged input rows. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

private theorem signed_length (z : ℤ) : (intCode z).length = z.natAbs.size+3 := by
  simp [intCode,intData,prodCode,pairBits_length,boolCode,Nat.size_eq_bits_len]
  omega

private theorem readAt_mem_or_default {α : Type} (d : α) (xs : List α) (i : ℕ) :
    readAt d xs i ∈ xs ∨ readAt d xs i=d := by
  by_cases h : i<xs.length
  · left
    simp [readAt,List.getElem?_eq_getElem h]
  · right
    simp [readAt,List.drop_eq_nil_iff.mpr (Nat.le_of_not_gt h)]

/-- Every binary coefficient in an arbitrarily ragged encoded matrix fits in the
entire encoded input. The zero obtained from either kind of out-of-bounds read also fits. -/
theorem entryAt_size_le_matrix_word (A : IntMatrix) (i j : ℕ) :
    (entryAt A i j).natAbs.size ≤ (intMatrixCode A).length := by
  rcases readAt_mem_or_default [] A i with hr | hr
  · change rowAt A i ∈ A at hr
    rcases readAt_mem_or_default 0 (rowAt A i) j with hz | hz
    · change entryAt A i j ∈ rowAt A i at hz
      have h : (intCode (entryAt A i j)).length ≤ (intMatrixCode A).length :=
        (code_le_of_mem intCode hz).trans (code_le_of_mem intRowCode hr)
      rw [signed_length] at h; omega
    · change entryAt A i j=0 at hz; simp [hz]
  · change rowAt A i=[] at hr; simp [entryAt,hr,readAt]

/-- Exact list and element frames are included in this quadratic table estimate. -/
theorem square_word_bound (n b : ℕ) (f : ℕ → ℕ → ℤ)
    (cells : ∀ i<n, ∀ j<n, (f i j).natAbs.size≤b) :
    (intMatrixCode ((List.range n).map fun i => (List.range n).map (f i))).length ≤
      n*(2*(n*(2*(b+3)+2)+1)+2)+1 := by
  unfold intMatrixCode
  apply (listCode_length_map_bound intRowCode (fun i => (List.range n).map (f i))
    (List.range n) (n*(2*(b+3)+2)+1) ?_).trans_eq (by simp)
  intro i hi
  unfold intRowCode
  apply (listCode_length_map_bound intCode (f i) (List.range n) (b+3) ?_).trans_eq (by simp)
  intro j hj
  rw [signed_length]
  exact Nat.add_le_add_right (cells i (List.mem_range.mp hi) j (List.mem_range.mp hj)) 3

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.PrimalDual.Finite
import OAI.Optimization.LinearProgramming.PrimalDual.JointDatum
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.SplitIfs

/-! Physical scalar-word layout of the input and the joint matrix produced by the RAM. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

variable {K : Type*} {m d : ℕ}

private def flatEntry (A : Matrix (Fin m) (Fin d) K) (k : Fin (m*d)) : K :=
  A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

private theorem flatEntry_row (A : Matrix (Fin m) (Fin d) K) (i : Fin m) (j : Fin d)
    (h : i.val*d+j.val < m*d) : flatEntry A ⟨i.val*d+j.val, h⟩ = A i j := by
  have he : (⟨i.val*d+j.val, h⟩ : Fin (m*d)) = finProdFinEquiv (i,j) := by
    apply Fin.ext; change i.val*d+j.val = j.val+d*i.val; ac_rfl
  simp [he, flatEntry]

private theorem flat_words (A : Matrix (Fin m) (Fin d) K) :
    (List.ofFn fun i => List.ofFn (A i)).flatten = List.ofFn (flatEntry A) := by
  rw [List.ofFn_mul (flatEntry A)]
  simp only [flatEntry_row]

theorem lpInput_length (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) :
    (lpInput A b).length = m*d+m := by simp [lpInput, flat_words]

private theorem row_addr_lt (i : Fin m) (j : Fin d) : i.val*d+j.val < m*d := by
  calc i.val*d+j.val < i.val*d+d := Nat.add_lt_add_left j.isLt _
       _ = (i.val+1)*d := by rw [Nat.add_mul, one_mul]
       _ ≤ m*d := Nat.mul_le_mul_right _ i.isLt

/-- Row-major matrix and RHS access, before any objective vector is appended. -/
theorem lpInput_matrix_word (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (i : Fin m) (j : Fin d) :
    (lpInput A b)[i.val*d+j.val]? = some (A i j) := by
  simp [lpInput, flat_words, List.getElem?_append, row_addr_lt i j, flatEntry_row]

theorem lpInput_rhs_word (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (i : Fin m) :
    (lpInput A b)[m*d+i.val]? = some (b i) := by
  simp [lpInput, flat_words]

variable [Zero K]

/-- Scalar word on the optimization input tape at address `k`. -/
def optInputWord (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (c : Fin d → K) (k : Nat) : K :=
  ((lpInput A b ++ List.ofFn c)[k]?).getD 0

@[simp] theorem optInputWord_matrix (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (c : Fin d → K)
    (i : Fin m) (j : Fin d) : optInputWord A b c (i.val*d+j.val) = A i j := by
  have h := row_addr_lt i j
  simp [optInputWord, List.getElem?_append_left (show i.val*d+j.val < (lpInput A b).length by
    rw [lpInput_length]; omega), lpInput_matrix_word]

@[simp] theorem optInputWord_rhs (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (c : Fin d → K)
    (i : Fin m) : optInputWord A b c (m*d+i.val) = b i := by
  simp [optInputWord, List.getElem?_append_left (show m*d+i.val < (lpInput A b).length by
    rw [lpInput_length]; omega), lpInput_rhs_word]

@[simp] theorem optInputWord_obj (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (c : Fin d → K)
    (j : Fin d) : optInputWord A b c (m*d+m+j.val) = c j := by
  simp [optInputWord, lpInput_length]

@[simp] private theorem row_primal (i : Fin m) :
    (jointRowEquiv m d (.inl i)).val = i := rfl
@[simp] private theorem row_nonneg (i : Fin m) :
    (jointRowEquiv m d (.inr (.inl i))).val = m+i := rfl
@[simp] private theorem row_dualPos (j : Fin d) :
    (jointRowEquiv m d (.inr (.inr (.inl j)))).val = m+m+j := by
  change m+(m+j.val) = _; omega
@[simp] private theorem row_dualNeg (j : Fin d) :
    (jointRowEquiv m d (.inr (.inr (.inr (.inl j))))).val = m+m+d+j := by
  change m+(m+(d+j.val)) = _; omega
@[simp] private theorem row_gap (z : Unit) :
    (jointRowEquiv m d (.inr (.inr (.inr (.inr z))))).val = m+m+d+d := by
  cases z
  change m+(m+(d+(d+0))) = _; omega

section
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Reading the signed source word selected by each matrix-cell descriptor yields
the entry of the finite joint matrix on which the oracle is called. -/
theorem jointDatum_matrix (A : Matrix (Fin m) (Fin d) F) (b : Fin m → F) (c : Fin d → F)
    (r : Fin (m+(m+(d+(d+1))))) (j : Fin (d+m)) :
    (jointDatum m d r.val j.val).read (optInputWord A b c) = finJointMatrix A b c r j := by
  obtain ⟨r, rfl⟩ := (jointRowEquiv m d).surjective r
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [finJointMatrix, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases r with i | i | k | k | z <;> rcases j with j | i' <;>
    simp only [row_primal, row_nonneg, row_dualPos, row_dualNeg, row_gap,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd,
      jointMatrix, Sum.elim_inl, Sum.elim_inr, Fin.ext_iff, jointDatum] <;>
    split_ifs <;> first | (exfalso; omega) | simp [JointDatum.read]
  all_goals split_ifs <;> simp_all <;> omega

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- The descriptor at the column immediately after the variables is the RHS word. -/
theorem jointDatum_rhs (A : Matrix (Fin m) (Fin d) F) (b : Fin m → F) (c : Fin d → F)
    (r : Fin (m+(m+(d+(d+1))))) :
    (jointDatum m d r.val (d+m)).read (optInputWord A b c) = finJointRhs b c r := by
  obtain ⟨r,rfl⟩ := (jointRowEquiv m d).surjective r
  simp only [finJointRhs, Function.comp_apply, Equiv.symm_apply_apply]
  rcases r with i | i | j | j | z <;>
    simp only [row_primal, row_nonneg, row_dualPos, row_dualNeg, row_gap,
      jointRhs, Sum.elim_inl, Sum.elim_inr, jointDatum] <;>
    split_ifs <;> first | (exfalso; omega) | simp [JointDatum.read]

end
end PrimalDual
end LinearProgramming
end Optimization
end OAI

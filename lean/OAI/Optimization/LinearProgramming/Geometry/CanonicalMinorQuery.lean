import OAI.Optimization.LinearProgramming.Geometry.MinorKeys
import OAI.Optimization.LinearProgramming.Elimination.Basic

/-! Checked canonical indices of nonzero primal prefix minors. This procedure reads
only a sorted key and the original matrix, independently of pivot rounding and Gram computations. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace Canonical

open Matrix

variable {r s n : ℕ}

/-- Evaluate the sorted key with the tabulated determinant. A successful lookup includes
the proof that the chosen minor is nonzero. -/
def checkedPrimalMinor (D : Matrix (Fin r) (Fin n) ℚ)
    (E : Matrix (Fin s) (Fin n) ℚ) (key : ℕ × Finset (Fin n)) :
    Option (Compression.NonzeroPairMinor D E) :=
  match canonicalPrefixIndex r key with
  | none => none
  | some u =>
    if hn : Elimination.determinant (D.submatrix u.2.1 u.2.2) = 0 then none
    else some ⟨.inl u, by change (D.submatrix _ _).det ≠ 0; simpa only [Elimination.determinant_eq] using hn⟩

theorem checkedPrimalMinor_value (D : Matrix (Fin r) (Fin n) ℚ)
    (E : Matrix (Fin s) (Fin n) ℚ) (f : Compression.NonzeroPairMinor D E → ℚ) (key : ℕ × Finset (Fin n)) :
    (checkedPrimalMinor D E key).elim 0 f = prefixAssignment D E f key := by
  classical
  unfold checkedPrimalMinor prefixAssignment
  cases hk : canonicalPrefixIndex r key with
  | none => rfl
  | some u =>
    simp only [Elimination.determinant_eq, Compression.pairMinorValue]
    split
    · rename_i h; simp [h]
    · rename_i h; simp [h]; rfl

end Canonical
end Geometry
end LinearProgramming
end Optimization
end OAI

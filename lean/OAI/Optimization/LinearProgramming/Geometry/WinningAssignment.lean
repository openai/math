import OAI.Optimization.LinearProgramming.Geometry.RegisteredCircuits
import OAI.Optimization.LinearProgramming.Geometry.RationalSubspace

/-! The hidden sign is fixed by the rational row spaces even when the admissible
minor assignment changes after a restart. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix Submodule Compression PriceGame
open scoped Matrix

variable {N r s : ℕ}

/-- The range bound for a full canonical assignment also bounds all totalized prefix lookups. -/
theorem prefixAssignment_bounds (D : Matrix (Fin r) (Fin N) ℚ) (E : Matrix (Fin s) (Fin N) ℚ)
    (f : NonzeroPairMinor D E → ℚ) {F : ℝ} (hF : 0 ≤ F) (hb : ∀ u, |(f u : ℝ)| ≤ F)
    (key : ℕ × Finset (Fin N)) :
    |(prefixAssignment D E f key : ℝ)| ≤ F ∧ |(dualPrefixAssignment D E f key : ℝ)| ≤ F := by
  classical
  constructor
  · unfold prefixAssignment
    split
    · simpa using hF
    · split
      · exact hb _
      · simpa using hF
  · unfold dualPrefixAssignment
    split
    · simpa using hF
    · split
      · exact hb _
      · simpa using hF

/-- Every positive coordinate of an arbitrary full-height circuit family has a finite
cost in the range `[0, 2F]` if all returned values are bounded by `F`. -/
theorem minorCircuitFamily_costBound (A : Matrix (Fin r) (Fin N) ℚ)
    (g : ℕ × Finset (Fin N) → ℚ) {F : ℝ} (hb : ∀ key, |(g key : ℝ)| ≤ F)
    (i : Fin N) (hi : 0 < circuitEnvelope (minorCircuitFamily A g) i) :
    circuitCost (minorCircuitFamily A g) i ∈ Set.Icc 0 (2*F) := by
  cases r with
  | zero => simp [minorCircuitFamily, fullCircuitFamily, circuitEnvelope] at hi
  | succ k => exact circuitCost_mem_Icc (A.map (Rat.castHom ℝ)) _ (fun J j _ => hb (prefixMinorKey J j)) i hi

/-- The active set defined by any one assignment is the rational row-space support set. -/
theorem minorCircuitFamily_active_iff (A : Matrix (Fin r) (Fin N) ℚ)
    (hA : LinearIndependent ℚ A.row) (g : ℕ × Finset (Fin N) → ℚ) (i : Fin N) :
    0 < circuitEnvelope (minorCircuitFamily A g) i ↔
      ∃ x ∈ span ℚ (Set.range A.row), 0 ≤ x ∧ 0 < x i :=
  (fullCircuitEnvelope_pos_iff (A.map (Rat.castHom ℝ)) (independent_rows_map _ A hA) _ i).trans
    (rational_row_witness_iff_real A hA i).symm

/-- The sign and support in the price game depend only on the two original subspaces. -/
theorem exists_winning_circuit_side (D : Matrix (Fin r) (Fin N) ℚ) (E : Matrix (Fin s) (Fin N) ℚ)
    (hD : LinearIndependent ℚ D.row) (hE : LinearIndependent ℚ E.row)
    (hDE : D * Eᵀ = 0) (hsize : r+s=N) (anchor : Fin N) :
    ∃ flag : Bool, (flag = true ↔ ∃ x ∈ span ℚ (Set.range D.row), 0 ≤ x ∧ 0 < x anchor) ∧
      ∀ f g, 0 < circuitEnvelope (if flag then minorCircuitFamily D f else minorCircuitFamily E g) anchor := by
  classical
  have horth := complementary_rowSpan D E hD hE hDE hsize
  have halt := Farkas.subspace_coordinate_alternative (span ℚ (Set.range D.row)) anchor
  rw [← horth] at halt
  by_cases h : ∃ x ∈ span ℚ (Set.range D.row), 0 ≤ x ∧ 0 < x anchor
  · exact ⟨true, iff_of_true rfl h, fun f _ => (minorCircuitFamily_active_iff D hD f anchor).2 h⟩
  · have hy := Classical.not_not.mp (halt.not.mp h)
    exact ⟨false, iff_of_false (by decide) h, fun _ g => (minorCircuitFamily_active_iff E hE g anchor).2 hy⟩

end Geometry
end LinearProgramming
end Optimization
end OAI

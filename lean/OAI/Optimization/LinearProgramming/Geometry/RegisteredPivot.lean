import OAI.Optimization.LinearProgramming.Geometry.PivotBasis
import OAI.Optimization.LinearProgramming.Geometry.Admissible

/-! All the normalized prefix rows used in a label test refer to one global minor assignment. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix Submodule SignType
open scoped Matrix

variable {κ : Type*} {a n r s : ℕ}

namespace PivotSystemSpec

private theorem register_extension {D : Matrix (Fin r) (Fin n) ℚ} {price : Fin n → ℚ}
    {localLogs : PivotKey n → ℚ} {ha : a ≤ r} {rows : Fin a → PivotRow n}
    (cert : PivotSystemSpec D price localLogs ha rows) (ell g : κ → ℝ) (v : Fin a)
    (matchLog : ∀ j, (rows v).raw j ≠ 0 → ∃ u, g u = localLogs (prefixMinorKey (earlierPivots rows v) j)
      ∧ ell u = Real.logb 2 |((rows v).raw j : ℝ)|) :
    RegisteredVector (span ℝ (Set.range (D.map (Rat.castHom ℝ)).row)) ell g
      (fun j => (price j : ℝ)) (exactPivotFrameRow rows price localLogs v) := by
  let σ := sign (((rows v).raw (rows v).pivot : ℚ) : ℝ)
  have hσ : |(σ : ℝ)| ≤ 1 := by cases σ <;> norm_num [SignType.cast]
  exact ⟨fun j => ((rows v).raw j : ℝ),
    fun j => (localLogs (prefixMinorKey (earlierPivots rows v) j) : ℝ), (σ : ℝ),
    cert.raw_mem_realRowSpan v, hσ, fun j hj => matchLog j (fun hz => hj (by simp [hz])), rfl⟩

/-- Registration of the exact oriented row produced by each *primal* pivot stage. -/
theorem exactPivotFrameRow_registered {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}
    {price : Fin n → ℚ} {f : Compression.NonzeroPairMinor D E → ℚ}
    {ha : a ≤ r} {rows : Fin a → PivotRow n} (cert : PivotSystemSpec D price (prefixAssignment D E f) ha rows)
    (v : Fin a) : RegisteredVector (span ℝ (Set.range (D.map (Rat.castHom ℝ)).row))
      (pairMinorLog D E) (fun u => (f u : ℝ)) (fun j => (price j : ℝ))
      (exactPivotFrameRow rows price (prefixAssignment D E f) v) := by
  apply register_extension cert
  intro j hj
  rw [(cert.stage v).minors] at hj ⊢
  obtain ⟨u, hu, hlog⟩ := prefixAssignment_matches D E f (Nat.le_trans v.isLt ha) (earlierPivots rows v) j hj
  exact ⟨u, congrArg ((↑) : ℚ → ℝ) hu, hlog⟩

/-- The dual normalized frame uses the same canonical minor type and global values. The
caller supplies the opposite prices when constructing the dual pivot run. -/
theorem exactPivotFrameRow_dualRegistered {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}
    {price : Fin n → ℚ} {f : Compression.NonzeroPairMinor D E → ℚ}
    {ha : a ≤ s} {rows : Fin a → PivotRow n} (cert : PivotSystemSpec E price (dualPrefixAssignment D E f) ha rows)
    (v : Fin a) : RegisteredVector (span ℝ (Set.range (E.map (Rat.castHom ℝ)).row))
      (pairMinorLog D E) (fun u => (f u : ℝ)) (fun j => (price j : ℝ))
      (exactPivotFrameRow rows price (dualPrefixAssignment D E f) v) := by
  apply register_extension cert
  intro j hj
  rw [(cert.stage v).minors] at hj ⊢
  obtain ⟨u, hu, hlog⟩ := dualPrefixAssignment_matches D E f (Nat.le_trans v.isLt ha) (earlierPivots rows v) j hj
  exact ⟨u, congrArg ((↑) : ℚ → ℝ) hu, hlog⟩

end PivotSystemSpec
end Geometry
end LinearProgramming
end Optimization
end OAI

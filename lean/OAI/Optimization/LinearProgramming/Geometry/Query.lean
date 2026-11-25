import OAI.Optimization.LinearProgramming.Geometry.PivotBasis
import OAI.Optimization.LinearProgramming.Geometry.GramAlgorithm
import OAI.Optimization.LinearProgramming.Geometry.LabelBasis

/-! The concrete designated-coordinate minor-query program. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix
open scoped Matrix

variable {r n : ℕ}

/-- Complete the price query on one designated coordinate.  A restart during any
pivot request aborts via `MinorQuery.Run`.  The no-pivot branch is unreachable for
row-independent inputs, including an empty basis. -/
def geometricMinorLabel (D : Matrix (Fin r) (Fin n) ℚ) (t : Fin n → ℚ) (i : Fin n) :
    MinorQuery (PivotKey n) Bool :=
  (pivotPrefix D t r le_rfl).bind fun
    | none => .done false
    | some rows =>
      let tables := roundedPivotMatrix rows t (geoCutoff n)
      let P := computeGramProjector tables
      .done (fwLabel (1 - P) i)

theorem geometricMinorLabel_bounded (D : Matrix (Fin r) (Fin n) ℚ)
    (t : Fin n → ℚ) (i : Fin n) : (geometricMinorLabel D t i).Bounded (r*n) := by
  unfold geometricMinorLabel
  apply MinorQuery.bounded_mono (MinorQuery.bounded_bind _ _ (pivotPrefix_bounded ..) (m := 0) ?_)
    (by omega)
  rintro (_ | rows) <;> exact True.intro

theorem geometricMinorLabel_run_length (D : Matrix (Fin r) (Fin n) ℚ)
    (t : Fin n → ℚ) (i : Fin n) {log out}
    (hrun : MinorQuery.Run (geometricMinorLabel D t i) log out) :
    log.length + MinorQuery.restartCost out ≤ r*n :=
  hrun.call_bound (geometricMinorLabel_bounded ..)

theorem geometricMinorLabel_eval (D : Matrix (Fin r) (Fin n) ℚ)
    (hD : LinearIndependent ℚ D.row) (f : PivotKey n → ℚ) (t : Fin n → ℚ) (i : Fin n) :
    ∃ rows : Fin r → PivotRow n, PivotSystemSpec D t f le_rfl rows ∧
      MinorQuery.eval f (geometricMinorLabel D t i) =
        fwLabel (1 - rowGramProjector (roundedPivotMatrix rows t (geoCutoff n))) i := by
  obtain ⟨rows, he, hs⟩ := pivotPrefix_eval D t f r le_rfl hD
  refine ⟨rows, hs, ?_⟩
  simp only [geometricMinorLabel, MinorQuery.eval_bind, he, MinorQuery.eval, computeGramProjector_eq]

end Geometry
end LinearProgramming
end Optimization
end OAI

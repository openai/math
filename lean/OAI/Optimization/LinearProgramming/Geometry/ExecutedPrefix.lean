import OAI.Optimization.LinearProgramming.Geometry.LabelTheorem

/-! The mathematical output of the postprocessing RAM on a concrete completed prefix. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix Compression
open scoped Matrix

variable {r s n : ℕ}

/-- The physical rounded table from a successful row-prefix transcript produces exactly
this geometric oracle output under every assignment extending the answers. -/
theorem geometricLabel_of_prefix_run (D : Matrix (Fin r) (Fin n) ℚ)
    (E : Matrix (Fin s) (Fin n) ℚ) (f : NonzeroPairMinor D E → ℚ)
    (t : Fin n → ℚ) (i : Fin n) (rows : Fin r → PivotRow n) (xs : List (PivotKey n × ℚ))
    (run : MinorQuery.Run (pivotPrefix D t r le_rfl) xs (.inr (some rows)))
    (answers : ∀ e ∈ xs, prefixAssignment D E f e.1 = e.2) :
    MinorQuery.eval f (geometricLabel D E t i) =
      fwLabel (1 - rowGramProjector (roundedPivotMatrix rows t (geoCutoff n))) i := by
  have h := run.eval_of_extends _ answers
  simp only [geometricLabel_eval, geometricMinorLabel, MinorQuery.eval_bind, h,
    MinorQuery.eval, computeGramProjector_eq]

/-- A successful price-query label satisfies both circuit-envelope implications under
every common clipped assignment extending its physical transcript. -/
theorem completedPrefix_circuit_labels (D : Matrix (Fin r) (Fin n) ℚ)
    (E : Matrix (Fin s) (Fin n) ℚ) (hD : LinearIndependent ℚ D.row)
    (hE : LinearIndependent ℚ E.row) (hrank : r+s=n) (hDE : D*Eᵀ=0)
    (f : NonzeroPairMinor D E → ℚ)
    (hclip : FourLogAccuracy (geoCutoff n : ℝ) (pairMinorLog D E) (fun u => (f u : ℝ)))
    (q : PriceGame.Query n) (rows : Fin r → PivotRow n) (xs : List (PivotKey n × ℚ))
    (run : MinorQuery.Run (pivotPrefix D q.prices r le_rfl) xs (.inr (some rows)))
    (answers : ∀ e ∈ xs, prefixAssignment D E f e.1 = e.2) :
    let result := fwLabel (1-rowGramProjector (roundedPivotMatrix rows q.prices (geoCutoff n))) q.index
    ValidNearLabel (minorCircuitFamily D (prefixAssignment D E f)) true q result ∧
      ValidNearLabel (minorCircuitFamily E (dualPrefixAssignment D E f)) false q result := by
  have labels := geometricLabel_correct_assignment D E hD hE hrank hDE f hclip q
  simpa only [geometricLabel_of_prefix_run D E f q.prices q.index rows xs run answers] using labels

end Geometry
end LinearProgramming
end Optimization
end OAI

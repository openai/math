import OAI.Optimization.LinearProgramming.Geometry.QueryKeys
import OAI.Optimization.LinearProgramming.Geometry.RegisteredPivot
import OAI.Optimization.LinearProgramming.Geometry.RegisteredCircuits
import OAI.Optimization.LinearProgramming.Geometry.Hidden

/-! Proposition 2.1. The only numerical assumption on a full assignment is the
four-term clipping guarantee. Every output on an interrupted or completed run
is accounted for by the single-coordinate minor-query semantics. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix Submodule Compression PriceGame
open scoped BigOperators Matrix

variable {r s n : ℕ}

theorem geoDelta_eq (n : ℕ) : geoDelta n = (1 / 2 : ℝ) ^ geoCutoff n := by
  simp [geoDelta, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), inv_pow]

private theorem neg_rat_prices (t : Fin n → ℚ) :
    (fun j => (((-t) j : ℚ) : ℝ)) = -(fun j => (t j : ℝ)) := by
  ext j
  simp

/-- With all replies given by one full minor assignment, the deterministic
rational query returns the appropriate sign at every active near-minimizer.
No basis-conditioning, approximation, or sign-oracle hypotheses are inputs. -/
theorem geometricLabel_correct_assignment
    (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (hD : LinearIndependent ℚ D.row) (hE : LinearIndependent ℚ E.row)
    (hrank : r + s = n) (hDE : D * Eᵀ = 0)
    (f : NonzeroPairMinor D E → ℚ)
    (hclip : FourLogAccuracy (geoCutoff n : ℝ) (pairMinorLog D E) (fun u => (f u : ℝ)))
    (q : PriceGame.Query n) :
    let answer := MinorQuery.eval f (geometricLabel D E q.prices q.index)
    ValidNearLabel (minorCircuitFamily D (prefixAssignment D E f)) true q answer ∧
      ValidNearLabel (minorCircuitFamily E (dualPrefixAssignment D E f)) false q answer := by
  classical
  let ft := prefixAssignment D E f
  let gt := dualPrefixAssignment D E f
  let t : Fin n → ℝ := fun j => q.prices j
  let C := minorCircuitFamily D ft
  let C' := minorCircuitFamily E gt
  obtain ⟨rows, hrows, hlabel⟩ := geometricMinorLabel_eval D hD ft q.prices q.index
  obtain ⟨dualRows, _, hdual⟩ := pivotPrefix_eval E (-q.prices) gt s le_rfl hE
  let d := roundedPivotMatrix rows q.prices (geoCutoff n)
  let e := roundedPivotMatrix dualRows (-q.prices) (geoCutoff n)
  let W := span ℝ (Set.range (D.map (Rat.castHom ℝ)).row)
  let V := span ℝ (Set.range (E.map (Rat.castHom ℝ)).row)
  have horth : D.map (Rat.castHom ℝ) * (E.map (Rat.castHom ℝ))ᵀ = 0 := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, hDE]
    simp
  have hr₁ : ∀ j, RoundedRegistered W (pairMinorLog D E) (fun u => (f u : ℝ))
      t (geoDelta n) ((d.map (Rat.castHom ℝ)).row j) := by
    intro j
    refine ⟨exactPivotFrameRow rows q.prices ft j, hrows.exactPivotFrameRow_registered j, ?_⟩
    intro l
    change |((d j l : ℚ) : ℝ) - exactPivotFrameRow rows q.prices ft j l| ≤ geoDelta n
    rw [geoDelta_eq]
    exact hrows.rounded_approximates_extension (geoCutoff n) j l
  have hr₂ : ∀ j, RoundedRegistered V (pairMinorLog D E) (fun u => (f u : ℝ))
      (-t) (geoDelta n) ((e.map (Rat.castHom ℝ)).row j) := by
    intro j
    refine ⟨exactPivotFrameRow dualRows (-q.prices) gt j, ?_, ?_⟩
    · simpa only [neg_rat_prices, t] using hdual.exactPivotFrameRow_dualRegistered j
    · intro l
      change |((e j l : ℚ) : ℝ) - exactPivotFrameRow dualRows (-q.prices) gt j l| ≤ geoDelta n
      rw [geoDelta_eq]
      exact hdual.rounded_approximates_extension (geoCutoff n) j l
  have H := label_of_registered_frames (pairMinorLog D E) (fun u => (f u : ℝ)) hclip
    (fun a ha b hb => rowSpan_dot_eq_zero _ _ horth ha hb) d e _ _
    (hrows.isPivotFrame (geoCutoff n)) (hdual.isPivotFrame (geoCutoff n)) hrank t hr₁ hr₂ C C'
    (fun c hc j => (minorCircuitFamily_unitCube D ft hc j).1)
    (fun c hc j => (minorCircuitFamily_unitCube E gt hc j).1)
    (fun _ hc => registered_primal_circuit D E f t hc)
    (fun _ hc => registered_dual_circuit D E f (-t) hc) q.index
  dsimp only
  rw [geometricLabel_eval, hlabel]
  constructor
  · intro hi hnear
    exact H.1 ⟨hi, hnear⟩
  · intro hi hnear
    exact H.2 ⟨hi, by simpa [t, sub_eq_add_neg] using hnear⟩

/-- Successful-query form of Proposition 2.1. A fresh, possibly retrospective
assignment only has to agree with the answers actually read by this query. -/
theorem geometricLabel_correct
    (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (hD : LinearIndependent ℚ D.row) (hE : LinearIndependent ℚ E.row)
    (hrank : r + s = n) (hDE : D * Eᵀ = 0) (q : PriceGame.Query n)
    {log b} (hrun : MinorQuery.Run (geometricLabel D E q.prices q.index) log (.inr b))
    (f : NonzeroPairMinor D E → ℚ)
    (hread : ∀ a ∈ log, f a.1 = a.2)
    (hclip : FourLogAccuracy (geoCutoff n : ℝ) (pairMinorLog D E) (fun u => (f u : ℝ))) :
    ValidNearLabel (minorCircuitFamily D (prefixAssignment D E f)) true q b ∧
      ValidNearLabel (minorCircuitFamily E (dualPrefixAssignment D E f)) false q b := by
  rw [← hrun.eval_of_extends f hread]
  exact geometricLabel_correct_assignment D E hD hE hrank hDE f hclip q

end Geometry
end LinearProgramming
end Optimization
end OAI

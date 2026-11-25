import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

namespace OAI
/-! The distance from a product plane to an apex above its second coordinate. -/

namespace ThreeFlat

open WithLp

/-- At zero first coordinate and positive second-coordinate distance, the product
distance has the same slope as the second-coordinate distance. -/
theorem hasGradientAt_sqrt_sum_sq {f : ℝ → ℝ} {y : ℝ} (hfy : 0 < f y)
    (hdiff : DifferentiableAt ℝ f y) :
    HasGradientAt (fun p : WithLp 2 (ℝ × ℝ) ↦ Real.sqrt (p.fst ^ 2 + (f p.snd) ^ 2))
      (toLp 2 (0, deriv f y)) (toLp 2 (0, y)) := by
  let z := toLp 2 ((0 : ℝ), y)
  have h₁ : HasFDerivAt (fun p : WithLp 2 (ℝ × ℝ) ↦ p.fst) (fstL 2 ℝ ℝ ℝ) z :=
    (fstL 2 ℝ ℝ ℝ).hasFDerivAt
  have h₂ : HasFDerivAt (fun p : WithLp 2 (ℝ × ℝ) ↦ f p.snd)
      (deriv f y • sndL 2 ℝ ℝ ℝ) z :=
    hdiff.hasDerivAt.comp_hasFDerivAt_of_eq z (sndL 2 ℝ ℝ ℝ).hasFDerivAt rfl
  have hn : z.fst ^ 2 + (f z.snd) ^ 2 ≠ 0 := by simp [z, hfy.ne']
  apply hasGradientAt_iff_hasFDerivAt.mpr
  apply (((h₁.pow 2).add (h₂.pow 2)).sqrt hn).congr_fderiv
  ext p
  simp [z, Real.sqrt_sq hfy.le, InnerProductSpace.toDual_apply_apply, nsmul_eq_mul, smul_eq_mul]
  field_simp [hfy.ne']

end ThreeFlat

end OAI

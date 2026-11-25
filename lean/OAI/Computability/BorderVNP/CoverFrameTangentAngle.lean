import OAI.Computability.BorderVNP.CoverFrameDisintegration
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Physical unit tangent angle and its Haar law in the frame coordinates -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

open MeasureTheory Matrix UpperHalfPlane
open scoped ComplexConjugate

/-- Squaring the circle parameter is onto, including the negative real direction. -/
theorem circle_square_surjective : Function.Surjective (fun w : Circle => w^2) := by
  intro w
  refine ⟨Circle.exp ((w : ℂ).arg / 2), ?_⟩
  change Circle.exp ((w : ℂ).arg / 2) ^ 2 = w
  rw [pow_two, ← Circle.exp_add, add_halves]
  apply Circle.coe_injective
  simpa using Complex.norm_mul_exp_arg_mul_I (w : ℂ)

/-- Passing from a spin frame to a physical direction preserves angular Haar probability. -/
theorem square_preserving : MeasurePreserving (fun w : Circle => w^2) Epoch.angularHaar Epoch.angularHaar := by
  have hH : Epoch.angularHaar.IsHaarMeasure := by unfold Epoch.angularHaar; infer_instance
  let p : Circle →* Circle := powMonoidHom 2
  have hp : Continuous p := continuous_id.pow 2
  have hH' := Measure.isHaarMeasure_map_of_isFiniteMeasure Epoch.angularHaar p hp circle_square_surjective
  have hP' := (Measure.isProbabilityMeasure_map_iff hp.measurable.aemeasurable).mpr
    (inferInstance : IsProbabilityMeasure Epoch.angularHaar)
  exact ⟨hp.measurable, Measure.isHaarMeasure_eq_of_isProbabilityMeasure
    (Epoch.angularHaar.map p) Epoch.angularHaar⟩

/-- Position and physical orientation have independent laws in the product frame chart. -/
theorem physicalAngle_preserving (l : ℕ) : MeasurePreserving
    (fun p : ℍ × Circle => (p.1,p.2^2)) ((positionLaw l).prod Epoch.angularHaar)
    ((positionLaw l).prod Epoch.angularHaar) := (MeasurePreserving.id _).prod square_preserving

private theorem denom_spin_frame (z : ℍ) (w : Circle) :
    denom ((z.toSL2R * spin w : SL) : GL (Fin 2) ℝ) I = ((w⁻¹ : Circle) : ℂ) / ↑(Real.sqrt z.im) := by
  have ha : (z.toSL2R * spin w) 1 0 = (1/Real.sqrt z.im) * -(w : ℂ).im := by
    change ((z.toSL2R : Mat) * (spin w : Mat)) 1 0 = _
    simp [spin, Matrix.mul_apply, Fin.sum_univ_two]
  have hb : (z.toSL2R * spin w) 1 1 = (1/Real.sqrt z.im) * (w : ℂ).re := by
    change ((z.toSL2R : Mat) * (spin w : Mat)) 1 1 = _
    simp [spin, Matrix.mul_apply, Fin.sum_univ_two]
  rw [Circle.coe_inv_eq_conj]
  change (↑((z.toSL2R * spin w) 1 0) : ℂ) * Complex.I + ↑((z.toSL2R * spin w) 1 1) = _
  rw [ha,hb]
  apply Complex.ext <;>
    simp [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.mul_im, mul_comm]

/-- The differential of the Möbius action maps the reference unit horizontal tangent
at `I` to the Euclidean vector `z.im * w²`. Dividing by the local metric scale `z.im`
therefore gives the physical unit direction `w²`. -/
theorem derivative_spin_frame (z : ℍ) (w : Circle) :
    deriv (fun x : ℂ => (((z.toSL2R * spin w) • ofComplex x : ℍ) : ℂ)) (I : ℍ) =
      ↑z.im * (w : ℂ)^2 := by
  let g := (z.toSL2R * spin w : SL)
  have h := deriv_smul (g := (g : GL (Fin 2) ℝ)) (by simp) I
  change deriv (fun x : ℂ => (((g : GL (Fin 2) ℝ) • ofComplex x : ℍ) : ℂ)) (I : ℍ) = _
  rw [h, show (g : GL (Fin 2) ℝ).val.det = 1 from g.property]
  rw [denom_spin_frame, div_pow, Circle.coe_inv, inv_pow]
  have hs : (↑(Real.sqrt z.im) : ℂ)^2 = ↑z.im := by exact_mod_cast Real.sq_sqrt z.im_pos.le
  simp [hs, div_eq_mul_inv, mul_comm]

end Cover.Frame

end BorderVNP
end Computability
end OAI

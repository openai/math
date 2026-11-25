import OAI.Computability.BorderVNP.CoverFrameQuotientTopology
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.Analysis.Complex.Circle

/-! # Position and fiber coordinates for real special-linear frames

The standard section of the action at `I` has positive diagonal. The remaining matrix
fixes `I` and is precisely a unit complex rotation. This circle is the double cover of the
physical unit tangent circle; a fiber parameter `w` rotates a tangent vector by `w²`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

open Matrix UpperHalfPlane

/-- Standard orthogonal matrices fixing `I` in the upper half plane. -/
noncomputable def spin (w : Circle) : SL :=
  ⟨!![(w : ℂ).re, (w : ℂ).im; -(w : ℂ).im, (w : ℂ).re], by
    simpa [Matrix.det_fin_two, Complex.normSq_apply] using w.normSq_coe⟩

/-- Multiplication on the rotation circle agrees with multiplication of its frame matrices. -/
theorem spin_mul (a b : Circle) : spin (a*b) = spin a * spin b := by
  apply Subtype.ext
  change (spin (a*b) : Mat) = (spin a : Mat) * (spin b : Mat)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spin, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- A point in the rotation fiber fixes `I`. -/
theorem spin_fixes_I (w : Circle) : spin w • I = I := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply, div_eq_iff (mod_cast denom_ne_zero (spin w) I)]
  simp [spin]
  ring_nf
  simp

/-- The stabilizer equation over the complex numbers determines both diagonal and
both off-diagonal entries of the matrix. -/
private theorem stabilizer_entries (g : SL) (h : g • I = I) :
    g 1 1 = g 0 0 ∧ g 1 0 = -g 0 1 := by
  have he := congrArg UpperHalfPlane.coe h
  rw [coe_specialLinearGroup_apply, div_eq_iff (mod_cast denom_ne_zero g I)] at he
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  simp [Complex.mul_re, Complex.mul_im] at hr hi
  constructor <;> linarith

/-- Recover the unit complex number from a matrix in the stabilizer. -/
noncomputable def spinOf (g : SL) (hg : g • I = I) : Circle :=
  ⟨⟨g 0 0, g 0 1⟩, by
    apply mem_sphere_zero_iff_norm.mpr
    have h := g.property
    rw [Matrix.det_fin_two] at h
    obtain ⟨hd,hc⟩ := stabilizer_entries g hg
    change g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 at h
    rw [hd,hc] at h
    have hs : Complex.normSq (⟨g 0 0, g 0 1⟩ : ℂ) = 1 := by simpa [Complex.normSq_apply] using h
    rw [Complex.normSq_eq_norm_sq] at hs
    nlinarith [norm_nonneg (⟨g 0 0, g 0 1⟩ : ℂ)]⟩

/-- Extracting the circle coordinate and forming its matrix recovers the stabilizer element. -/
theorem spin_spinOf (g : SL) (hg : g • I = I) : spin (spinOf g hg) = g := by
  obtain ⟨hd,hc⟩ := stabilizer_entries g hg
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spin, spinOf, hc, hd]

/-- Removing the section from a frame leaves an element of the rotation stabilizer. -/
theorem section_residual_fixes (g : SL) : ((g • I).toSL2R⁻¹ * g) • I = I := by
  rw [mul_smul, inv_smul_eq_iff, toSL2R_smul_I]

/-- Fiber parameter of a real frame, relative to the canonical positive-diagonal section. -/
noncomputable def spinCoordinate (g : SL) : Circle :=
  spinOf ((g • I).toSL2R⁻¹ * g) (section_residual_fixes g)

/-- Reconstruction of a frame from its position and fiber parameter. -/
theorem section_mul_spinCoordinate (g : SL) : (g • I).toSL2R * spin (spinCoordinate g) = g := by
  rw [spinCoordinate, spin_spinOf, mul_inv_cancel_left]

/-- Recovering the fiber parameter is continuous. -/
theorem continuous_spinCoordinate : Continuous spinCoordinate := by
  have h : Continuous fun g : SL => (g • I).toSL2R⁻¹ * g :=
    (continuous_toSL2R.comp (continuous_id.smul continuous_const)).inv.mul continuous_id
  apply Continuous.subtype_mk
  have hm : Continuous fun g : SL => (⟨g 0 0, g 0 1⟩ : ℂ) := by
    have he (g : SL) : (⟨g 0 0, g 0 1⟩ : ℂ) = ↑(g 0 0) + ↑(g 0 1) * Complex.I := by
      apply Complex.ext <;> simp
    simp_rw [he]
    fun_prop
  exact hm.comp h

/-- Continuity of the frame matrix of a unit complex rotation. -/
theorem continuous_spin : Continuous spin := by
  apply Continuous.subtype_mk
  change Continuous fun z : Circle => !![(z : ℂ).re,(z : ℂ).im;-(z : ℂ).im,(z : ℂ).re]
  fun_prop

/-- The real frame group splits as position and a circular fiber. -/
noncomputable def frameCoordinates : SL ≃ₜ ℍ × Circle where
  toFun g := (g • I, spinCoordinate g)
  invFun p := p.1.toSL2R * spin p.2
  left_inv := section_mul_spinCoordinate
  right_inv p := by
    have h : (p.1.toSL2R * spin p.2) • I = p.1 := by rw [mul_smul, spin_fixes_I, toSL2R_smul_I]
    apply Prod.ext h
    apply Circle.coe_injective
    change (spinCoordinate (p.1.toSL2R * spin p.2) : ℂ) = _
    change (⟨(((_ • I).toSL2R)⁻¹ * (p.1.toSL2R * spin p.2)) 0 0,
      (((_ • I).toSL2R)⁻¹ * (p.1.toSL2R * spin p.2)) 0 1⟩ : ℂ) = _
    rw [h, inv_mul_cancel_left]
    rfl
  continuous_toFun := (continuous_id.smul continuous_const).prodMk continuous_spinCoordinate
  continuous_invFun := (continuous_toSL2R.comp continuous_fst).mul (continuous_spin.comp continuous_snd)

/-- Left translation in frame coordinates changes the base point by the Möbius action
and rotates its circle fiber by a factor depending only on the old base point. -/
theorem translate_frameCoordinates (g : SL) (p : ℍ × Circle) :
    frameCoordinates (g * frameCoordinates.symm p) =
      (g • p.1, spinCoordinate (g * p.1.toSL2R) * p.2) := by
  apply frameCoordinates.symm.injective
  rw [Homeomorph.symm_apply_apply]
  change g * (p.1.toSL2R * spin p.2) = (g • p.1).toSL2R * spin (_ * _)
  rw [spin_mul, ← mul_assoc, ← mul_assoc]
  have h := section_mul_spinCoordinate (g*p.1.toSL2R)
  rw [mul_smul, toSL2R_smul_I] at h
  rw [h]

end Cover.Frame

end BorderVNP
end Computability
end OAI

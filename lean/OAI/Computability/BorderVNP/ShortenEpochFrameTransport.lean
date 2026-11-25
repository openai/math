import OAI.Computability.BorderVNP.ShortenEpochGeodesic
import OAI.Computability.BorderVNP.CoverFrameCoordinates

/-!
# Transport of both endpoints by an actual arithmetic frame motion

The Cayley coordinate turns the rotation subgroup fixing `I` into ordinary
multiplication by the square of its circle parameter. In the spatial
hyperboloid chart this rotates the entire unit-speed geodesic, including
both endpoints. Thus finite frame mixing applies to the directions of
the actual oriented segments in the product host.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open Cover.Frame UpperHalfPlane
open scoped ComplexConjugate

private noncomputable def diskCoord (z : UpperHalfPlane) : ℂ :=
  ((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)

private theorem disk_den_ne (z : UpperHalfPlane) : (z : ℂ) + Complex.I ≠ 0 := by
  intro hz
  have h := congrArg Complex.im hz
  simp at h
  linarith only [h,z.im_pos]

private theorem disk_injective : Function.Injective diskCoord := by
  intro x y he
  unfold diskCoord at he
  have h := (div_eq_div_iff (disk_den_ne x) (disk_den_ne y)).mp he
  apply UpperHalfPlane.ext
  have h' : ((x : ℂ) - y) * (2 * Complex.I) = 0 := by linear_combination h
  exact sub_eq_zero.mp (mul_eq_zero.mp h' |>.resolve_right (mul_ne_zero (by norm_num) Complex.I_ne_zero))

private theorem disk_tangentChart (v : ℂ) :
    diskCoord (tangentChart v) = -Complex.I * v / ((timeCoord v : ℂ) + 1) := by
  let t := timeCoord v
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht1 : (t : ℂ)+1 ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp at h
    linarith
  have htsq : t^2 = 1+v.re^2+v.im^2 := Real.sq_sqrt (by positivity)
  have hd : t-v.im ≠ 0 := by
    intro he
    rw [sub_eq_zero.mp he] at htsq
    nlinarith only [htsq,sq_nonneg v.re]
  unfold diskCoord
  apply (div_eq_div_iff (disk_den_ne _) ht1).mpr
  change ((⟨v.re/(t-v.im),1/(t-v.im)⟩ : ℂ) - Complex.I) * (t+1) =
    -Complex.I * v * ((⟨v.re/(t-v.im),1/(t-v.im)⟩ : ℂ)+Complex.I)
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> field_simp <;>
    nlinarith only [htsq]

private theorem disk_spin (w : Circle) (z : UpperHalfPlane) :
    diskCoord (spin w • z) = (w : ℂ)^2 * diskCoord z := by
  let a : ℂ := ((w : ℂ).re : ℝ)
  let b : ℂ := ((w : ℂ).im : ℝ)
  let n := a*(z : ℂ)+b
  let d := -b*(z : ℂ)+a
  have hden : d ≠ 0 := by
    have h := denom_ne_zero (spin w) z
    change ((-(w : ℂ).im : ℝ) : ℂ) * (z : ℂ) + ((w : ℂ).re : ℂ) ≠ 0 at h
    simpa only [Complex.ofReal_neg] using h
  have hsm : ((spin w • z : UpperHalfPlane) : ℂ) = n/d := by
    rw [coe_specialLinearGroup_apply]
    change (((w : ℂ).re : ℂ) * (z : ℂ) + ((w : ℂ).im : ℂ)) /
      (((-(w : ℂ).im : ℝ) : ℂ) * (z : ℂ) + ((w : ℂ).re : ℂ)) = _
    rw [Complex.ofReal_neg]
  have hplus : n+Complex.I*d = conj (w : ℂ) * ((z:ℂ)+Complex.I) := by
    have hw : conj (w : ℂ) = a-Complex.I*b := by apply Complex.ext <;> simp [a,b,Complex.mul_re,Complex.mul_im]
    rw [hw]
    dsimp [n,d]
    linear_combination b * Complex.I_mul_I
  have hminus : n-Complex.I*d = (w:ℂ)*((z:ℂ)-Complex.I) := by
    have hw : (w : ℂ) = a+Complex.I*b := by apply Complex.ext <;> simp [a,b,Complex.mul_re,Complex.mul_im]
    rw [hw]
    dsimp [n,d]
    linear_combination b * Complex.I_mul_I
  have hunit : (w:ℂ) * conj (w:ℂ) = 1 := by rw [Complex.mul_conj, Circle.normSq_coe]; norm_num
  unfold diskCoord
  rw [hsm, div_sub' hden, mul_comm d Complex.I, div_add' n Complex.I d hden, div_div_div_cancel_right₀ hden, hplus,hminus]
  have hn : conj (w:ℂ) ≠ 0 := by intro he; simp [he] at hunit
  rw [mul_div_mul_comm]
  congr 1
  apply (div_eq_iff hn).mpr
  linear_combination -(w:ℂ) * hunit

private theorem timeCoord_eq_norm (v : ℂ) : timeCoord v = Real.sqrt (1+‖v‖^2) := by
  simp only [timeCoord,Complex.sq_norm,Complex.normSq_apply]
  congr 1
  ring

/-- The spin coordinate acts by its square on the whole unit-speed geodesic. -/
theorem spin_tangentLine (w : Circle) (u : ℂ) (t : ℝ) :
    spin w • tangentLine u t = tangentLine ((w:ℂ)^2 * u) t := by
  apply disk_injective
  rw [disk_spin, tangentLine, tangentLine,disk_tangentChart,disk_tangentChart]
  have hv : Real.sinh t • ((w:ℂ)^2 * u) = (w:ℂ)^2 * (Real.sinh t • u) := by
    rw [Complex.real_smul,Complex.real_smul]; ring
  rw [hv,timeCoord_eq_norm,timeCoord_eq_norm,norm_mul,norm_pow,Circle.norm_coe,one_pow,one_mul]
  ring

/-- The standard frame section gives exactly the affine center shift of the
hyperboloid chart. -/
theorem section_smul_eq_shiftFactor (c z : UpperHalfPlane) : c.toSL2R • z = shiftFactor c z := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  have hn : (Real.sqrt c.im : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr c.im_pos).ne'
  rw [shiftFactor, coe_vadd, coe_pos_real_smul, Complex.real_smul]
  change (((Real.sqrt c.im : ℝ) : ℂ)*(z : ℂ) + ((c.re / Real.sqrt c.im : ℝ) : ℂ)) /
    (((0:ℝ) : ℂ)*(z : ℂ) + ((1 / Real.sqrt c.im : ℝ) : ℂ)) = _
  rw [Complex.ofReal_zero,zero_mul,zero_add,Complex.ofReal_div,Complex.ofReal_div,Complex.ofReal_one]
  field_simp
  have hsq : (Real.sqrt c.im : ℂ)^2 = (c.im : ℂ) := by exact_mod_cast Real.sq_sqrt c.im_pos.le
  linear_combination (z : ℂ) * hsq

/-- Applying a whole-network motion to a framed geodesic translates its
center and rotates its tangent direction by the same physical fiber action
that appears in the Haar angle law. -/
theorem frame_smul_tangentLine (g : SL) (u : ℂ) (t : ℝ) :
    g • tangentLine u t = shiftFactor (g • I) (tangentLine (((spinCoordinate g : Circle) : ℂ)^2*u) t) := by
  calc
    _ = ((g • I).toSL2R * spin (spinCoordinate g)) • tangentLine u t := by rw [section_mul_spinCoordinate]
    _ = _ := by rw [mul_smul, spin_tangentLine, section_smul_eq_shiftFactor]

end Epoch

end BorderVNP
end Computability
end OAI

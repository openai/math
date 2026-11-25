import OAI.Computability.BorderVNP.CoverLorentzMatrix
import Mathlib.NumberTheory.Niven
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# The quaternion rotation in the frame correspondence

The norm-one quaternion `(-5+2k)/7` is a member of a diagonal conjugate of
the real rotation group. Niven's theorem rules out a rational rotation
angle, so any closed subgroup containing it contains the entire circle.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

open Matrix Set Filter Real
open scoped Matrix Topology

/-- The real frame group before dividing out its central sign. -/
abbrev SL := SpecialLinearGroup (Fin 2) ℝ

/-- Rotations in the coordinates of the real splitting of the quaternion order. -/
noncomputable def rotation (t : ℝ) : SL :=
  ⟨!![cos t, √3 * sin t; -sin t / √3, cos t], by
    have h : √(3:ℝ) ≠ 0 := by positivity
    simp [det_fin_two]; field_simp; nlinarith [sin_sq_add_cos_sq t]⟩

/-- The elliptic generator of §5.2, given by its angle in the rotation group. -/
noncomputable def elliptic : SL := rotation (arccos (-5/7))

private theorem sqrt_three_sq : (√(3:ℝ))^2 = 3 := sq_sqrt (by norm_num)
private theorem sqrt_two_sq : (√(2:ℝ))^2 = 2 := sq_sqrt (by norm_num)

private theorem sin_angle : sin (arccos (-5/7)) = (2*√2) * √3 / 7 := by
  rw [sin_arccos]
  have h : 0 ≤ ((2*√(2:ℝ)) * √3 / 7) := by positivity
  apply (sq_eq_sq₀ (sqrt_nonneg _) h).mp
  rw [sq_sqrt (by norm_num)]
  ring_nf; rw [sqrt_two_sq, sqrt_three_sq]; norm_num

/-- Seven times the elliptic generator is exactly the integral matrix of `-5+2k`. -/
theorem elliptic_numerator : (7 : ℝ) • (elliptic : Mat) = split ⟨-5,0,0,2⟩ := by
  have h : √(3:ℝ) ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [elliptic, rotation, split, cos_arccos (by norm_num : (-1:ℝ) ≤ -5/7)
      (by norm_num : (-5:ℝ)/7 ≤ 1), sin_angle] <;>
    field_simp
  ring_nf
  exact sqrt_three_sq

/-- Angle addition is matrix multiplication. -/
theorem rotation_add (s t : ℝ) : rotation (s+t) = rotation s * rotation t := by
  have h : √(3:ℝ) ≠ 0 := by positivity
  apply Subtype.ext
  change (rotation (s+t) : Mat) = (rotation s : Mat) * (rotation t : Mat)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, cos_add, sin_add, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- Rotation through a full turn is the identity. -/
theorem rotation_two_pi : rotation (2*π) = 1 := by
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotation]

/-- Rotation through zero is the identity. -/
theorem rotation_zero : rotation 0 = 1 := by
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotation]

/-- Reversing the angle inverts the rotation. -/
theorem rotation_neg (t : ℝ) : rotation (-t) = (rotation t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← rotation_add, neg_add_cancel, rotation_zero]

/-- The frame rotation depends continuously on its real angle. -/
theorem continuous_rotation : Continuous rotation := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem irrational_angle : Irrational (arccos (-5/7) / (2*π)) := by
  rintro ⟨q,hq⟩
  have hx : cos (arccos (-5/7)) = -5/7 := cos_arccos (by norm_num) (by norm_num)
  have hy : arccos (-5/7) = ((2*q : ℚ):ℝ) * π := by
    push_cast
    rw [eq_div_iff (by positivity : (2*π:ℝ)≠0)] at hq
    linarith
  have nv := niven ⟨2*q,hy⟩ ⟨-5/7, by simpa using hx⟩
  rw [hx] at nv
  norm_num at nv

/-- Every closed subgroup of the real frame group containing the quaternion contains
all the rotations fixing its center. -/
theorem all_rotation_mem {H : Subgroup SL} (hclosed : IsClosed (H : Set SL))
    (hz : elliptic ∈ H) (t : ℝ) : rotation t ∈ H := by
  let angles : AddSubgroup ℝ :=
    { carrier := rotation ⁻¹' H
      zero_mem' := by change rotation 0 ∈ H; rw [rotation_zero]; exact H.one_mem
      add_mem' := fun {a b} ha hb => by
        change rotation (a+b) ∈ H; rw [rotation_add]; exact H.mul_mem ha hb
      neg_mem' := fun {a} ha => by change rotation (-a) ∈ H; rw [rotation_neg]; exact H.inv_mem ha }
  have hpair : AddSubgroup.closure {arccos (-5/7), 2*π} ≤ angles := by
    apply (AddSubgroup.closure_le _).mpr
    apply Set.pair_subset_iff.mpr
    refine ⟨hz, ?_⟩
    change rotation (2*π) ∈ H
    rw [rotation_two_pi]; exact H.one_mem
  have hd := (dense_addSubgroupClosure_pair_iff.mpr irrational_angle).mono hpair
  have ht := hd t
  change t ∈ closure (rotation ⁻¹' (H : Set SL)) at ht
  rwa [(hclosed.preimage continuous_rotation).closure_eq] at ht

end Cover.Frame

end BorderVNP
end Computability
end OAI

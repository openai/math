import OAI.Computability.BorderVNP.ShortenEpochFrameTransport
import OAI.Computability.BorderVNP.ShortenEpochSegments
import OAI.Computability.BorderVNP.CoverFrameTangentAngle

/-!
# Framed segments and factor-permuting motions

Each oriented product segment is represented by one actual determinant-one
frame and one scalar speed per factor. A single factor permutation followed
by componentwise Möbius motions transforms both ends by acting on these
frames. The transformed geodesic uses exactly the physical angles of the
frame mixing argument and the permuted speeds.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open Cover.Frame UpperHalfPlane

variable {I : Type*} [Fintype I]

/-- Product segment formed by moving the reference horizontal geodesic
with an actual spin frame in each factor. -/
noncomputable def framePoint (speed : I → ℝ) (f : I → SL) (t : ℝ) : HyperbolicHost I :=
  WithLp.toLp 2 fun i => f i • tangentLine 1 (t * speed i)

/-- The physical tangent coordinate of a framed product segment, including speeds. -/
noncomputable def frameVelocity (speed : I → ℝ) (f : I → SL) : PiLp 2 fun _ : I => ℂ :=
  WithLp.toLp 2 fun i => speed i • (((spinCoordinate (f i) : Circle) : ℂ)^2)

omit [Fintype I] in
/-- Actual frame action on the reference geodesic agrees with the full
geodesic in the squared-angle chart used to choose the bins. -/
theorem framePoint_chart (speed : I → ℝ) (hs : ∀ i, 0 ≤ speed i) (f : I → SL) (t : ℝ) :
    framePoint speed f t = shiftTo (WithLp.toLp 2 fun i => f i • UpperHalfPlane.I)
      (productLine (frameVelocity speed f) t) := by
  ext1 i
  let u : ℂ := ((spinCoordinate (f i) : Circle) : ℂ)^2
  have hu : ‖u‖ = 1 := by simp [u, norm_pow]
  change f i • tangentLine 1 (t * speed i) = shiftFactor _
    (tangentLine (unitDirection (speed i • u)) (t * ‖speed i • u‖))
  rw [factor_speed _ hu (hs i), frame_smul_tangentLine, mul_one]

/-- The chosen spin frame of a specified center and tangent direction. Its square
recovers the physical angle, including the fixed angle used at zero speed. -/
noncomputable def frameOfTangent (c : UpperHalfPlane) (v : ℂ) : SL :=
  c.toSL2R * spin ((circle_square_surjective
    (⟨unitDirection v, mem_sphere_zero_iff_norm.mpr (unitDirection_norm v)⟩ : Circle)).choose)

omit [Fintype I] in
/-- The chosen frame follows exactly the geodesic specified by the product tangent,
with the norm of each component as its speed. -/
theorem framePoint_ofTangent (c : HyperbolicHost I) (v : PiLp 2 (fun _ : I => ℂ)) (t : ℝ) :
    framePoint (fun i => ‖v i‖) (fun i => frameOfTangent (c i) (v i)) t = shiftTo c (productLine v t) := by
  ext1 i
  let w : Circle := ⟨unitDirection (v i),mem_sphere_zero_iff_norm.mpr (unitDirection_norm _)⟩
  let root := (circle_square_surjective w).choose
  have hroot : root^2 = w := (circle_square_surjective w).choose_spec
  change ((c i).toSL2R * spin root) • tangentLine 1 (t*‖v i‖) =
    shiftFactor _ (tangentLine (unitDirection (v i)) (t*‖v i‖))
  rw [mul_smul,spin_tangentLine,section_smul_eq_shiftFactor,mul_one,← Circle.coe_pow,hroot]

/-- There is one tuple of frames and nonnegative component speeds for both
oppositely oriented endpoints of any nonzero-length product segment. -/
theorem exists_framed_segment (a b : HyperbolicHost I) (hab : a ≠ b) :
    ∃ (speed : I → ℝ) (f : I → SL), (∀ i, 0 ≤ speed i) ∧ (∑ i, (speed i)^2) = 1 ∧
      framePoint speed f (-(dist a b / 2)) = a ∧ framePoint speed f (dist a b / 2) = b := by
  obtain ⟨c,v,hv,ha,hb⟩ := exists_product_midpoint_line a b hab
  let f (i : I) := frameOfTangent (c i) (v i)
  let speed (i : I) := ‖v i‖
  have line (t : ℝ) : framePoint speed f t = shiftTo c (productLine v t) := framePoint_ofTangent c v t
  refine ⟨speed,f,fun i => norm_nonneg _,?_,(line _).trans ha,(line _).trans hb⟩
  rw [show (∑ i, (speed i)^2) = ‖v‖^2 from (PiLp.norm_sq_eq_of_L2 _ v).symm, hv,one_pow]

omit [Fintype I] in
/-- A factor permutation and independent frame motions act on both ends of
a whole network using the same choices, with exactly the permuted speeds. -/
theorem motion_framePoint (e : Equiv.Perm I) (g : I → SL) (speed : I → ℝ)
    (f : I → SL) (t : ℝ) :
    (WithLp.toLp 2 fun i => g i • framePoint speed f t (e i) : HyperbolicHost I) =
      framePoint (speed ∘ e) (fun i => g i * f (e i)) t := by
  ext1 i
  exact (mul_smul _ _ _).symm

end Epoch

end BorderVNP
end Computability
end OAI

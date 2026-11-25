import OAI.Computability.BorderVNP.CoverLorentzIndex
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Analysis.Real.Sqrt

/-!
# Real matrix representation of the congruence order

Over the reals, `i` is diagonal with entries `√2,-√2` and
`j` has off-diagonal entries `3,1`. We retain the integral coordinates for
the congruence computations and use this faithful representation in the geometric host.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Matrix
open scoped Matrix

/-- The real matrix algebra used to model the quaternion order. -/
abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

/-- Real splitting of the integral quaternion order. -/
noncomputable def split : Order →+* Mat where
  toFun x := !![(x.re : ℝ) + Real.sqrt 2*x.imI, 3*x.imJ + 3*Real.sqrt 2*x.imK;
                (x.imJ : ℝ) - Real.sqrt 2*x.imK, (x.re : ℝ) - Real.sqrt 2*x.imI]
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  map_mul' x y := by
    rcases x with ⟨a,b,c,d⟩
    rcases y with ⟨e,f,g,h⟩
    have ht := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [QuaternionAlgebra.mk_mul_mk,Matrix.mul_apply,Fin.sum_univ_two] <;>
      ring_nf <;> rw [ht] <;> ring

/-- The reduced norm becomes the ordinary matrix determinant. -/
theorem det_split (x : Order) : (split x).det = norm x := by
  rcases x with ⟨a,b,c,d⟩
  simp [Matrix.det_fin_two,split,norm]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- The integral representation is faithful. -/
theorem split_injective : Function.Injective split := by
  intro x y h
  have h' : norm (x-y) = 0 := by
    have e := det_split (x-y)
    rw [map_sub,h,sub_self, Matrix.det_zero] at e
    exact_mod_cast e.symm
  exact sub_eq_zero.mp (eq_zero_of_norm_eq_zero _ h')

/-- A real special-linear representation of the level group. -/
noncomputable def gammaSL (d : ℕ) : gamma d →* Matrix.SpecialLinearGroup (Fin 2) ℝ where
  toFun u := ⟨split (u : Orderˣ), by rw [det_split,u.2.1,Int.cast_one]⟩
  map_one' := Subtype.ext (map_one split)
  map_mul' x y := Subtype.ext (map_mul split x.val.val y.val.val)

/-- The represented congruence group acts faithfully in the real matrix model. -/
theorem gammaSL_injective (d : ℕ) : Function.Injective (gammaSL d) := by
  intro x y h
  exact Subtype.ext (Units.ext (split_injective (congrArg Subtype.val h)))

/-- The four coordinates of the basis matrices after multiplication on the right by `g`. -/
noncomputable def rightMatrix (g : Mat) : Matrix (Fin 4) (Fin 4) ℝ :=
  let t := Real.sqrt 2
  let a := g 0 0
  let b := g 0 1
  let c := g 1 0
  let d := g 1 1
  !![a,t*a,3*c,3*t*c; b,t*b,3*d,3*t*d;
     c,-t*c,a,-t*a; d,-t*d,b,-t*b]

/-- The covolume determinant of the four integral quaternion basis matrices after translation. -/
theorem det_rightMatrix (g : Mat) : (rightMatrix g).det = 24 * g.det^2 := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four, Matrix.det_fin_two]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply,
    show ((0 : Fin 4).succAbove (0 : Fin 3)) = 1 by decide,
    show ((0 : Fin 4).succAbove (1 : Fin 3)) = 2 by decide,
    show ((0 : Fin 4).succAbove (2 : Fin 3)) = 3 by decide,
    show ((1 : Fin 4).succAbove (0 : Fin 3)) = 0 by decide,
    show ((1 : Fin 4).succAbove (1 : Fin 3)) = 2 by decide,
    show ((1 : Fin 4).succAbove (2 : Fin 3)) = 3 by decide,
    show ((2 : Fin 4).succAbove (0 : Fin 3)) = 0 by decide,
    show ((2 : Fin 4).succAbove (1 : Fin 3)) = 1 by decide,
    show ((2 : Fin 4).succAbove (2 : Fin 3)) = 3 by decide,
    show ((3 : Fin 4).succAbove (0 : Fin 3)) = 0 by decide,
    show ((3 : Fin 4).succAbove (1 : Fin 3)) = 1 by decide,
    show ((3 : Fin 4).succAbove (2 : Fin 3)) = 2 by decide]
  simp [rightMatrix]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Multiplying an integral quaternion matrix on the right by `g` in row-major coordinates. -/
theorem rightMatrix_coordinates (g : Mat) (x : Order) :
    (rightMatrix g).mulVec ![(x.re:ℝ),x.imI,x.imJ,x.imK] =
      ![(split x*g) 0 0, (split x*g) 0 1, (split x*g) 1 0, (split x*g) 1 1] := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four,
      split, rightMatrix] <;> ring

end Cover

end BorderVNP
end Computability
end OAI

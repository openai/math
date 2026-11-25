import OAI.Optimization.LinearProgramming.Lattice.Projection
import Mathlib.Data.Matrix.Mul

/-! A rational matrix for the orthogonal complement projection at each rounding step. -/

open scoped BigOperators RealInnerProductSpace
open Submodule Matrix WithLp

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

variable {p : ℕ}

private theorem sup_span_residual (S : Submodule ℝ (EuclideanSpace ℝ (Fin p))) (z : Fin p → ℝ) :
    S ⊔ ℝ ∙ residual S z = S ⊔ ℝ ∙ toLp 2 z := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply (span_singleton_le_iff_mem ..).2
    exact (S ⊔ ℝ ∙ toLp 2 z).sub_mem (mem_sup_right (mem_span_singleton_self _))
      (mem_sup_left (S.starProjection_apply_mem _))
  · apply sup_le le_sup_left
    apply (span_singleton_le_iff_mem ..).2
    have h := (S ⊔ ℝ ∙ residual S z).add_mem
      (mem_sup_right (mem_span_singleton_self (residual S z)))
      (mem_sup_left (S.starProjection_apply_mem (toLp 2 z)))
    simpa only [residual, sub_add_cancel] using h

private theorem residual_sup_span (S : Submodule ℝ (EuclideanSpace ℝ (Fin p))) (z v : Fin p → ℝ) :
    residual (S ⊔ ℝ ∙ toLp 2 z) v =
      residual S v - (ℝ ∙ residual S z).starProjection (residual S v) := by
  let T := ℝ ∙ residual S z
  have hTS : T ≤ Sᗮ := (span_singleton_le_iff_mem ..).2 (sub_starProjection_mem_orthogonal _)
  have hproj : (S ⊔ T).starProjection (toLp 2 v) =
      S.starProjection (toLp 2 v) + T.starProjection (residual S v) := by
    apply eq_starProjection_of_mem_orthogonal
    · exact (S ⊔ T).add_mem (mem_sup_left (S.starProjection_apply_mem _))
        (mem_sup_right (T.starProjection_apply_mem _))
    · rw [← inf_orthogonal]
      change toLp 2 v - (_ + _) ∈ Sᗮ ⊓ Tᗮ
      rw [← sub_sub]
      exact ⟨Sᗮ.sub_mem (sub_starProjection_mem_orthogonal _)
        (hTS (T.starProjection_apply_mem _)), sub_starProjection_mem_orthogonal _⟩
  rw [← sup_span_residual S z]
  change toLp 2 v - (S ⊔ T).starProjection (toLp 2 v) = residual S v - _
  rw [hproj, ← sub_sub]
  rfl

/-- Matrix of the projection onto the complement of one rational direction. -/
def rationalLineComplement (u : Fin p → ℚ) : Matrix (Fin p) (Fin p) ℚ :=
  if u ⬝ᵥ u = 0 then 1
  else fun i j => (1 : Matrix (Fin p) (Fin p) ℚ) i j - u i * u j / (u ⬝ᵥ u)

private theorem rationalLineComplement_apply (u : Fin p → ℚ) (i j : Fin p) :
    rationalLineComplement u i j = (1 : Matrix (Fin p) (Fin p) ℚ) i j -
      u i * u j / (u ⬝ᵥ u) := by
  by_cases h : u ⬝ᵥ u = 0 <;> simp [rationalLineComplement, h]

/-- A rational projector obtained by eliminating the listed integer directions in order from
the tail of the list. The formula also handles linearly dependent or zero directions. -/
def rationalResidualMatrix : List (Fin p → ℤ) → Matrix (Fin p) (Fin p) ℚ
  | [] => 1
  | z :: zs =>
    let B := rationalResidualMatrix zs
    rationalLineComplement (B *ᵥ fun i => (z i : ℚ)) * B

/-- The span of the accumulated real images of the integer directions. -/
def integerDirectionSpan : List (Fin p → ℤ) → Submodule ℝ (EuclideanSpace ℝ (Fin p))
  | [] => ⊥
  | z :: zs => integerDirectionSpan zs ⊔ ℝ ∙ toLp 2 (realCoordinates z)

/-- Apply a rational matrix to real input registers, without inspecting their encodings. -/
noncomputable def realMatrixApply (A : Matrix (Fin p) (Fin p) ℚ) (v : Fin p → ℝ) : Fin p → ℝ :=
  (A.map (Rat.castHom ℝ)) *ᵥ v

private theorem apply_one (v : Fin p → ℝ) : realMatrixApply 1 v = v := by
  simp [realMatrixApply, Matrix.map_one]

private theorem apply_mul (A B : Matrix (Fin p) (Fin p) ℚ) (v : Fin p → ℝ) :
    realMatrixApply (A * B) v = realMatrixApply A (realMatrixApply B v) := by
  rw [realMatrixApply, ← RingHom.mapMatrix_apply, map_mul, ← Matrix.mulVec_mulVec]
  rfl

private theorem apply_integer (B : Matrix (Fin p) (Fin p) ℚ) (z : Fin p → ℤ) :
    (fun i => ((B *ᵥ fun j => (z j : ℚ)) i : ℝ)) =
      realMatrixApply B (realCoordinates z) := by
  ext i
  simp [realMatrixApply, Matrix.mulVec, dotProduct, realCoordinates]

private theorem real_lineComplement_apply (u : Fin p → ℚ) (v : Fin p → ℝ) :
    toLp 2 (realMatrixApply (rationalLineComplement u) v) =
      toLp 2 v - (ℝ ∙ toLp 2 (fun i => (u i : ℝ))).starProjection (toLp 2 v) := by
  let e : EuclideanSpace ℝ (Fin p) := toLp 2 (fun i => (u i : ℝ))
  have hinner : inner ℝ e (toLp 2 v) = ∑ i, (u i : ℝ) * v i := by
    simp [e, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hnorm : ‖e‖ ^ 2 = ((u ⬝ᵥ u : ℚ) : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ i, ‖(u i : ℝ)‖ ^ 2) = ((u ⬝ᵥ u : ℚ) : ℝ)
    simp only [Real.norm_eq_abs, sq_abs]
    simp only [pow_two, dotProduct, Rat.cast_sum, Rat.cast_mul]
  ext i
  change realMatrixApply (rationalLineComplement u) v i =
    (toLp 2 v - (ℝ ∙ e).starProjection (toLp 2 v)) i
  rw [Submodule.starProjection_singleton, hinner, hnorm]
  change (∑ j, ((rationalLineComplement u i j : ℚ) : ℝ) * v j) =
    v i - (∑ j, (u j : ℝ) * v j) / ((u ⬝ᵥ u : ℚ) : ℝ) * (u i : ℝ)
  simp only [rationalLineComplement_apply, Rat.cast_sub, Rat.cast_div, Rat.cast_mul, sub_mul,
    Finset.sum_sub_distrib]
  have hd : (∑ j : Fin p, (((1 : Matrix (Fin p) (Fin p) ℚ) i j : ℚ) : ℝ) * v j) = v i := by
    exact congrFun (apply_one v) i
  rw [hd, Finset.sum_div, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The rational matrix computes the actual real orthogonal residual for every real input.
No independence hypothesis, numerical oracle or real matrix inverse is needed. -/
theorem rationalResidualMatrix_correct (zs : List (Fin p → ℤ)) (v : Fin p → ℝ) :
    toLp 2 (realMatrixApply (rationalResidualMatrix zs) v) = residual (integerDirectionSpan zs) v := by
  induction zs generalizing v with
  | nil => simp [rationalResidualMatrix, integerDirectionSpan, apply_one, residual]
  | cons z zs ih =>
    let B := rationalResidualMatrix zs
    let S := integerDirectionSpan zs
    let u := B *ᵥ fun j => (z j : ℚ)
    have he : toLp 2 (fun i => (u i : ℝ)) = residual S (realCoordinates z) := by
      rw [show (fun i => (u i : ℝ)) = realMatrixApply B (realCoordinates z) from apply_integer B z]
      exact ih _
    change toLp 2 (realMatrixApply (rationalLineComplement u * B) v) =
      residual (S ⊔ ℝ ∙ toLp 2 (realCoordinates z)) v
    rw [apply_mul, real_lineComplement_apply, he, show toLp 2 (realMatrixApply B v) = _ from ih v,
      residual_sup_span]

end Lattice
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.Geometry.Oracle
import OAI.Optimization.LinearProgramming.Geometry.Projection
import OAI.Optimization.LinearProgramming.Geometry.Triangular
import Mathlib.LinearAlgebra.Matrix.Block

/-! Conditioning and independence of the rounded pivot matrices, including zero row rank. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Finset Matrix
open scoped BigOperators Matrix

variable {r n : ℕ}

/-- The three invariants preserved by pivot selection and entrywise rounding. -/
structure IsPivotFrame (D : Matrix (Fin r) (Fin n) ℝ) (p : Fin r → Fin n) : Prop where
  diagonal (i) : D i (p i) = 1
  vanishes (i j : Fin r) : i < j → D j (p i) = 0
  bounded (i j) : |D i j| ≤ 1

theorem IsPivotFrame.independent {D : Matrix (Fin r) (Fin n) ℝ} {p : Fin r → Fin n}
    (h : IsPivotFrame D p) : LinearIndependent ℝ D.row := by
  let R := D.submatrix id p
  have hupper : R.IsUpperTriangular := fun i j hij => h.vanishes j i hij
  have hdet : R.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hupper]
    simp [R, h.diagonal]
  let restrictCols : (Fin n → ℝ) →ₗ[ℝ] (Fin r → ℝ) :=
    LinearMap.pi fun j => LinearMap.proj (p j)
  apply LinearIndependent.of_comp restrictCols
  exact Matrix.linearIndependent_rows_of_det_ne_zero (hdet ▸ one_ne_zero)

/-- Every unit vector in the row span has a uniformly bounded actual coefficient
vector, even before one chooses an orthonormal basis for the span. -/
theorem IsPivotFrame.coeff_bound {D : Matrix (Fin r) (Fin n) ℝ} {p : Fin r → Fin n}
    (h : IsPivotFrame D p) (origin : Fin n) (hr : r ≤ n) (c : Fin r → ℝ)
    (hu : coordinateNorm (Dᵀ *ᵥ c) = 1) : ∑ i, |c i| ≤ 2^n := by
  let c' (j : ℕ) : ℝ := if hj : j < r then c ⟨j,hj⟩ else 0
  let D' (j : ℕ) (l : Fin n) : ℝ := if hj : j < r then D ⟨j,hj⟩ l else 0
  let p' (j : ℕ) : Fin n := if hj : j < r then p ⟨j,hj⟩ else origin
  let x := Dᵀ *ᵥ c
  have hcoord j : |x j| ≤ 1 := by
    apply abs_coordinate_le_of_squareLength_le zero_le_one
    change (∑ i, x i ^ 2) ≤ 1 ^ 2
    rw [← coordinateNorm_sq, show coordinateNorm x = 1 from hu]
  have rep (j : Fin n) : x j = ∑ i ∈ range r, c' i * D' i j := by
    change (∑ i : Fin r, D i j * c i) = _
    rw [sum_fin_eq_sum_range]
    apply sum_congr rfl
    intro a ha
    simp [c', D', mem_range.mp ha, mul_comm]
  have hbound := triangular_l1_bound r D' p' c' x
      (fun i hi => by simp [D', p', hi, h.diagonal])
      (fun i hi j hj hij => by simpa [D', p', hi, hj] using h.vanishes ⟨i,hi⟩ ⟨j,hj⟩ hij)
      (fun i hi j => by simpa [D', hi] using h.bounded ⟨i,hi⟩ j)
      hcoord rep
  have hsum : ∑ i : Fin r, |c i| = ∑ i ∈ range r, |c' i| := by
    rw [sum_fin_eq_sum_range]
    apply sum_congr rfl
    intro a ha
    simp [c', mem_range.mp ha]
  rw [hsum]
  exact hbound.trans ((sub_le_self _ zero_le_one).trans (pow_le_pow_right₀ (by norm_num) hr))

end Geometry
end LinearProgramming
end Optimization
end OAI

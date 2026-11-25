import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic
import OAI.Optimization.LinearProgramming.Geometry.ColumnBasis
import OAI.Optimization.LinearProgramming.Geometry.MinimalSupport

/-! Signed determinants of an arbitrary row prefix, as used in Section 2. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

variable {K : Type*}

open Matrix Submodule
open scoped BigOperators Matrix

variable {K ι : Type*} {k : ℕ}

/-- Append the queried column to a list of `k` columns of a matrix with `k+1` rows. -/
def circuitMinor [CommRing K] (D : Matrix (Fin (k + 1)) ι K) (J : Fin k → ι) (j : ι) : K :=
  (D.submatrix id (Fin.lastCases j J)).det

/-- The cofactor expansion gives an explicit combination of the rows, valid for every prefix. -/
theorem circuitMinor_eq_vecMul [CommRing K] (D : Matrix (Fin (k + 1)) ι K) (J : Fin k → ι) :
    circuitMinor D J = (fun r : Fin (k + 1) =>
      (-1 : K) ^ (r.val + k) * (D.submatrix r.succAbove J).det) ᵥ* D := by
  classical
  funext j
  rw [circuitMinor, Matrix.det_succ_column _ (Fin.last k)]
  simp only [Fin.val_last, Matrix.submatrix_apply, id_eq, Fin.lastCases_last,
    Matrix.submatrix_submatrix, Function.comp_def, Fin.succAbove_last, Fin.lastCases_castSucc,
    Matrix.vecMul, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Signed minors are in the row space for a matrix of any positive height. -/
theorem circuitMinor_mem_rowSpan [CommRing K] (D : Matrix (Fin (k + 1)) ι K) (J : Fin k → ι) :
    circuitMinor D J ∈ span K (Set.range D.row) := by
  rw [← range_vecMulLinear, circuitMinor_eq_vecMul]
  exact ⟨_, rfl⟩

/-- A column already in the list gives a repeated column and a zero minor. -/
@[simp] theorem circuitMinor_of_mem_columns [CommRing K] (D : Matrix (Fin (k + 1)) ι K)
    (J : Fin k → ι) (u : Fin k) : circuitMinor D J (J u) = 0 := by
  apply Matrix.det_zero_of_column_eq (Fin.ne_of_lt (Fin.castSucc_lt_last u))
  intro r
  simp

/-- Selecting fewer rows preserves membership in the row space of the original matrix. -/
theorem circuitMinor_rowPrefix_mem_rowSpan [CommRing K] {ρ : Type*} (D : Matrix ρ ι K)
    (rows : Fin (k + 1) → ρ) (J : Fin k → ι) :
    circuitMinor (D.submatrix rows id) J ∈ span K (Set.range D.row) := by
  apply Submodule.span_mono (s := Set.range (D.submatrix rows id).row) _
    (circuitMinor_mem_rowSpan _ J)
  rintro _ ⟨r, rfl⟩
  exact ⟨rows r, rfl⟩

/-- Row-space vectors are uniquely identified by their restriction to any nonsingular set
of columns. This also gives the exact scalar relating a minimal witness to its signed minors. -/
private theorem eq_of_restrict_columns [Field K] (D : Matrix (Fin (k + 1)) ι K)
    (cols : Fin (k + 1) → ι) {x y : ι → K} (hx : x ∈ span K (Set.range D.row))
    (hy : y ∈ span K (Set.range D.row)) (hcols : (D.submatrix id cols).det ≠ 0)
    (hxy : ∀ t, x (cols t) = y (cols t)) : x = y := by
  rw [← range_vecMulLinear] at hx hy
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  have h : (u ᵥ* (D.submatrix id cols)) = v ᵥ* (D.submatrix id cols) := funext hxy
  have huv := (Matrix.vecMul_injective_iff.mpr (Matrix.linearIndependent_rows_of_det_ne_zero hcols)) h
  rw [huv]

/-- With a nonsingular extension of the zero columns by `i`, the determinant vector gives
all components of the row-space witness in the same scale. -/
theorem eq_smul_circuitMinor [Field K] (D : Matrix (Fin (k + 1)) ι K) (J : Fin k → ι)
    (i : ι) (x : ι → K) (hx : x ∈ span K (Set.range D.row)) (hz : ∀ t, x (J t) = 0)
    (hi : circuitMinor D J i ≠ 0) : x = (x i / circuitMinor D J i) • circuitMinor D J := by
  let cols : Fin (k + 1) → ι := Fin.lastCases (motive := fun _ => ι) i J
  refine eq_of_restrict_columns D cols hx
    (Submodule.smul_mem _ (x i / circuitMinor D J i) (circuitMinor_mem_rowSpan D J))
    (show (D.submatrix id cols).det ≠ 0 from hi) ?_
  intro t
  refine Fin.lastCases ?_ (fun u => ?_) t
  · simp [cols, hi]
  · simp [cols, hz]

/-- Orient the determinant vector by the sign of its reference entry. -/
theorem circuitMinor_or_neg_nonnegative [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (D : Matrix (Fin (k + 1)) ι K) (J : Fin k → ι) (i : ι) (x : ι → K)
    (hx : x ∈ span K (Set.range D.row)) (hpos : 0 ≤ x) (hxi : 0 < x i)
    (hz : ∀ t, x (J t) = 0) (hi : circuitMinor D J i ≠ 0) :
    (0 ≤ circuitMinor D J ∧ 0 < circuitMinor D J i) ∨
      (0 ≤ -(circuitMinor D J) ∧ 0 < -circuitMinor D J i) := by
  have hx' := eq_smul_circuitMinor D J i x hx hz hi
  rcases lt_or_gt_of_ne hi with hi | hi
  · right
    refine ⟨fun j => ?_, neg_pos.mpr hi⟩
    have hj := hpos j
    rw [congrFun hx' j] at hj
    change 0 ≤ (x i / circuitMinor D J i) * circuitMinor D J j at hj
    exact neg_nonneg.mpr (nonpos_of_mul_nonneg_right hj (div_neg_of_pos_of_neg hxi hi))
  · left
    refine ⟨fun j => ?_, hi⟩
    have hj := hpos j
    rw [congrFun hx' j] at hj
    change 0 ≤ (x i / circuitMinor D J i) * circuitMinor D J j at hj
    exact nonneg_of_mul_nonneg_right hj (div_pos hxi hi)

/-- Row-space witnesses of two matrices with orthogonal rows have zero dot product. -/
theorem rowSpan_dot_eq_zero [CommRing K] [Fintype ι] {ρ σ : Type*} [Fintype ρ] [Fintype σ]
    (D : Matrix ρ ι K) (E : Matrix σ ι K) (hDE : D * Eᵀ = 0) {x y : ι → K}
    (hx : x ∈ span K (Set.range D.row)) (hy : y ∈ span K (Set.range E.row)) : x ⬝ᵥ y = 0 := by
  rw [← range_vecMulLinear] at hx hy
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  change (u ᵥ* D) ⬝ᵥ (v ᵥ* E) = 0
  rw [← E.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hDE,
    Matrix.zero_mulVec, dotProduct_zero]

/-- Orthogonality also holds for determinant vectors taken from independent row prefixes. -/
theorem circuitMinor_dot_eq_zero [CommRing K] [Fintype ι] {ρ σ : Type*}
    [Fintype ρ] [Fintype σ] {l : ℕ} (D : Matrix ρ ι K) (E : Matrix σ ι K)
    (hDE : D * Eᵀ = 0) (dr : Fin (k + 1) → ρ) (er : Fin (l + 1) → σ)
    (J : Fin k → ι) (L : Fin l → ι) :
    circuitMinor (D.submatrix dr id) J ⬝ᵥ circuitMinor (E.submatrix er id) L = 0 :=
  rowSpan_dot_eq_zero D E hDE (circuitMinor_rowPrefix_mem_rowSpan D dr J)
    (circuitMinor_rowPrefix_mem_rowSpan E er L)

/-- Every nonnegative row-space vector positive at `i` has a nonnegative full-height
signed-minor representative positive there. Its support is contained in that of the input. -/
theorem exists_nonnegative_circuitMinor [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Fintype ι] (D : Matrix (Fin (k + 1)) ι K) (hD : LinearIndependent K D.row)
    (i : ι) {x : ι → K} (hx : x ∈ span K (Set.range D.row)) (hx0 : 0 ≤ x) (hxi : 0 < x i) :
    ∃ J : Fin k → ι, Function.Injective J ∧
      (∀ j, x j = 0 → circuitMinor D J j = 0) ∧
      ((0 ≤ circuitMinor D J ∧ 0 < circuitMinor D J i) ∨
        (0 ≤ -(circuitMinor D J) ∧ 0 < -circuitMinor D J i)) := by
  obtain ⟨c, hc, hc0, hci, hxc, hline⟩ := exists_witness_support_line _ i hx hx0 hxi
  have hci' : 0 < c i := hci.symm ▸ hxi
  have hker (u : Fin (k + 1) → K) (hui : (u ᵥ* D) i = 0)
      (huz : ∀ j, c j = 0 → (u ᵥ* D) j = 0) : u = 0 := by
    have hu : u ᵥ* D ∈ span K (Set.range D.row) := by
      rw [← range_vecMulLinear]
      exact ⟨u, rfl⟩
    have hv := hline (u ᵥ* D) hu huz
    rw [hui, zero_div, zero_smul] at hv
    apply Matrix.vecMul_injective_iff.mpr hD
    simpa using hv
  obtain ⟨J, hJ, hz, hi⟩ := exists_circuit_columns D i c hc hci'.ne' hker
  have hf := eq_smul_circuitMinor D J i c hc hz hi
  refine ⟨J, hJ, ?_, circuitMinor_or_neg_nonnegative D J i c hc hc0 hci' hz hi⟩
  intro j hj
  have heq := congrFun hf j
  change c j = (c i / circuitMinor D J i) * circuitMinor D J j at heq
  exact (mul_eq_zero.mp ((hxc j hj).symm.trans heq).symm).resolve_left (div_ne_zero hci'.ne' hi)

end Geometry
end LinearProgramming
end Optimization
end OAI

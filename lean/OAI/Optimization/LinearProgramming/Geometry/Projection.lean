import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Projection estimates for the geometric label test

The columns of the two frames are orthonormal bases of the rounded row spaces.
Using rectangular matrices also covers empty frames. -/

open Matrix InnerProductSpace
open scoped BigOperators Matrix

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

variable {n r s : ℕ}

/-- Squared Frobenius length as a sum of coordinate squares. -/
def frobeniusSq (A : Matrix (Fin r) (Fin s) ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

theorem frobeniusSq_eq_trace (A : Matrix (Fin r) (Fin s) ℝ) :
    frobeniusSq A = (Aᵀ * A).trace := by
  unfold frobeniusSq Matrix.trace
  rw [Finset.sum_comm]
  simp [Matrix.mul_apply, Matrix.diag, pow_two]

/-- An orthonormal column frame gives a symmetric, idempotent projector of the
same trace as the number of columns. -/
theorem frame_projector_properties (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1) :
    (U * Uᵀ)ᵀ = U * Uᵀ ∧ (U * Uᵀ) * (U * Uᵀ) = U * Uᵀ ∧ (U * Uᵀ).trace = r := by
  refine ⟨by simp, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U Uᵀ, hU, Matrix.one_mul]
  · rw [Matrix.trace_mul_comm, hU, Matrix.trace_one, Fintype.card_fin]

/-- The trace identity for two symmetric idempotents whose ranks sum to the dimension. -/
theorem frobeniusSq_projector_defect (P Q : Matrix (Fin n) (Fin n) ℝ)
    (hPt : Pᵀ = P) (hQt : Qᵀ = Q) (hP : P * P = P) (hQ : Q * Q = Q)
    (htrace : P.trace + Q.trace = n) :
    frobeniusSq (P + Q - 1) = 2 * (P * Q).trace := by
  rw [frobeniusSq_eq_trace]
  simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one, hPt, hQt]
  simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one,
    hP, hQ, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin]
  rw [Matrix.trace_mul_comm Q P]
  linarith

/-- The trace of the product of the two frame projectors is the sum of squared
inner products between their basis columns. -/
theorem trace_projector_product (U : Matrix (Fin n) (Fin r) ℝ)
    (V : Matrix (Fin n) (Fin s) ℝ) :
    ((U * Uᵀ) * (V * Vᵀ)).trace = frobeniusSq (Uᵀ * V) := by
  rw [frobeniusSq_eq_trace, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    _ = (((U * Uᵀ) * V) * Vᵀ).trace := by simp only [Matrix.mul_assoc]
    _ = (Vᵀ * ((U * Uᵀ) * V)).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/-- Section 2's complementary-dimension Frobenius identity in explicit coordinates. -/
theorem complementary_frame_defect (U : Matrix (Fin n) (Fin r) ℝ)
    (V : Matrix (Fin n) (Fin s) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hrank : r + s = n) :
    frobeniusSq (U * Uᵀ + V * Vᵀ - 1) = 2 * frobeniusSq (Uᵀ * V) := by
  obtain ⟨Ut, Ui, Utr⟩ := frame_projector_properties U hU
  obtain ⟨Vt, Vi, Vtr⟩ := frame_projector_properties V hV
  rw [frobeniusSq_projector_defect _ _ Ut Vt Ui Vi (by rw [Utr, Vtr]; exact_mod_cast hrank),
    trace_projector_product]

/-- Bound all squared coordinate contributions from the cross-frame Gram matrix. -/
theorem complementary_frame_defect_le (U : Matrix (Fin n) (Fin r) ℝ)
    (V : Matrix (Fin n) (Fin s) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hrank : r + s = n) {ε : ℝ} (hcross : ∀ i j, |(Uᵀ * V) i j| ≤ ε) :
    frobeniusSq (U * Uᵀ + V * Vᵀ - 1) ≤ 2 * n ^ 2 * ε ^ 2 := by
  rw [complementary_frame_defect U V hU hV hrank]
  have hp : frobeniusSq (Uᵀ * V) ≤ ∑ _ : Fin r, ∑ _ : Fin s, ε ^ 2 := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hcross i j) 2
  have hrs : (r : ℝ) * s ≤ (n : ℝ) ^ 2 := by
    have hr : (r : ℝ) ≤ n := by exact_mod_cast (show r ≤ n by omega)
    have hs : (s : ℝ) ≤ n := by exact_mod_cast (show s ≤ n by omega)
    simpa [sq] using mul_le_mul hr hs (by positivity : 0 ≤ (s : ℝ)) (by positivity : 0 ≤ (n : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hp
  calc
    _ ≤ 2 * (r * (s * ε ^ 2)) := by linarith
    _ = 2 * (r * s) * ε ^ 2 := by ring
    _ ≤ _ := by gcongr

/-- Euclidean length of a coordinate vector, including coordinates of sign-changing rows. -/
noncomputable def coordinateNorm (x : Fin n → ℝ) : ℝ :=
  ‖WithLp.toLp 2 x‖

theorem coordinateNorm_sq (x : Fin n → ℝ) :
    coordinateNorm x ^ 2 = ∑ i, x i ^ 2 := by
  exact EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)

/-- The action on a vector is bounded by the Frobenius norm, directly by
Cauchy–Schwarz on each row. -/
theorem coordinateNorm_mulVec_le (A : Matrix (Fin r) (Fin s) ℝ) (x : Fin s → ℝ) :
    coordinateNorm (A *ᵥ x) ≤ Real.sqrt (frobeniusSq A) * coordinateNorm x := by
  have hF : 0 ≤ frobeniusSq A := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hx : 0 ≤ coordinateNorm x := norm_nonneg _
  have hs : coordinateNorm (A *ᵥ x) ^ 2 ≤ frobeniusSq A * coordinateNorm x ^ 2 := by
    rw [coordinateNorm_sq, coordinateNorm_sq]
    unfold frobeniusSq
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) x
  apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) hx)
  simpa [mul_pow, Real.sq_sqrt hF] using hs

/-- A uniform correlation estimate for orthonormal frames controls the
distance to the first space by the projection on the second. -/
theorem complementary_frame_residual_le (U : Matrix (Fin n) (Fin r) ℝ)
    (V : Matrix (Fin n) (Fin s) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hrank : r + s = n) (x : Fin n → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hcross : ∀ i j, |(Uᵀ * V) i j| ≤ ε) :
    coordinateNorm ((1 - U * Uᵀ) *ᵥ x) ≤ coordinateNorm ((V * Vᵀ) *ᵥ x) +
      2 * n * ε * coordinateNorm x := by
  let P := U * Uᵀ
  let Q := V * Vᵀ
  have hdefect := complementary_frame_defect_le U V hU hV hrank hcross
  have hsqrt : Real.sqrt (frobeniusSq (P + Q - 1)) ≤ 2 * n * ε := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    change frobeniusSq (U * Uᵀ + V * Vᵀ - 1) ≤ _
    exact hdefect.trans (by nlinarith [sq_nonneg ((n : ℝ) * ε)])
  have h := (coordinateNorm_mulVec_le (P + Q - 1) x).trans
    (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _))
  have hid : (1 - P) *ᵥ x = Q *ᵥ x - (P + Q - 1) *ᵥ x := by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]; abel
  change coordinateNorm ((1 - P) *ᵥ x) ≤ coordinateNorm (Q *ᵥ x) + _
  rw [hid]
  exact (norm_sub_le (WithLp.toLp 2 (Q *ᵥ x)) (WithLp.toLp 2 ((P + Q - 1) *ᵥ x))).trans
    (add_le_add_right h _)

/-- A vector with coordinates in the unit box has Euclidean length at most
the square root of the number of coordinates. -/
theorem coordinateNorm_le_sqrt_card (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    coordinateNorm x ≤ Real.sqrt n := by
  apply Real.le_sqrt_of_sq_le
  rw [coordinateNorm_sq]
  calc
    _ ≤ ∑ _ : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum; intro i _
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hx i) 2
    _ = _ := by simp

/-- Testing all unit vectors fixed by a symmetric projector bounds its projected length.
This includes the zero projector. -/
theorem coordinateNorm_projector_le_of_unit_test (P : Matrix (Fin n) (Fin n) ℝ)
    (hPt : Pᵀ = P) (hP : P * P = P) (y : Fin n → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (htest : ∀ w : Fin n → ℝ, P *ᵥ w = w → coordinateNorm w = 1 → |w ⬝ᵥ y| ≤ a) :
    coordinateNorm (P *ᵥ y) ≤ a := by
  let z := P *ᵥ y
  have hzfix : P *ᵥ z = z := by
    dsimp [z]; rw [Matrix.mulVec_mulVec, hP]
  have hzn : 0 ≤ coordinateNorm z := norm_nonneg _
  by_cases hz : coordinateNorm z = 0
  · change coordinateNorm z ≤ a
    simpa only [hz] using ha
  have hpos : 0 < coordinateNorm z := lt_of_le_of_ne hzn (Ne.symm hz)
  have hdot : z ⬝ᵥ y = coordinateNorm z ^ 2 := by
    have hsym := Matrix.dotProduct_transpose_mulVec P z y
    rw [hPt, hzfix, ← dotProduct_comm z y] at hsym
    rw [← hsym, coordinateNorm_sq]
    change (∑ i, z i * z i) = ∑ i, z i ^ 2
    simp only [sq]
  let w := (coordinateNorm z)⁻¹ • z
  have hwfix : P *ᵥ w = w := by simp [w, Matrix.mulVec_smul, hzfix]
  have hwunit : coordinateNorm w = 1 := by
    change ‖WithLp.toLp 2 ((coordinateNorm z)⁻¹ • z)‖ = 1
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    change (coordinateNorm z)⁻¹ * coordinateNorm z = 1
    exact inv_mul_cancel₀ hz
  have h := htest w hwfix hwunit
  change |((coordinateNorm z)⁻¹ • z) ⬝ᵥ y| ≤ a at h
  rw [smul_dotProduct, smul_eq_mul, hdot, sq, ← mul_assoc,
    inv_mul_cancel₀ hz, one_mul, abs_of_nonneg hzn] at h
  exact h

/-- The concrete constants in (2.5). The two projection and cross-frame
hypotheses are the estimates just before (2.5), prior to substituting delta. -/
theorem geometric_projection_bounds (U : Matrix (Fin n) (Fin r) ℝ)
    (V : Matrix (Fin n) (Fin s) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hrank : r + s = n) (hn : 0 < n) (x y : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hbudget : 30 * (n : ℝ)^3 * 4^n * δ ≤ 1 / (2000 * n))
    (hcross : ∀ i j, |(Uᵀ * V) i j| ≤ 10 * n * 4^n * δ)
    (hQx : coordinateNorm ((V * Vᵀ) *ᵥ x) ≤ 10 * n * 2^n * δ)
    (hPy : coordinateNorm ((U * Uᵀ) *ᵥ y) ≤ 10 * n * 2^n * δ) :
    coordinateNorm ((1 - U * Uᵀ) *ᵥ x) ≤ 1 / (2000 * n) ∧
    coordinateNorm ((U * Uᵀ) *ᵥ y) ≤ 1 / (2000 * n) := by
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have h2n : (2 : ℝ)^n ≤ 4^n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hxN : coordinateNorm x ≤ n := by
    refine (coordinateNorm_le_sqrt_card x hx).trans ?_
    exact Real.sqrt_le_iff.mpr ⟨hn0, by nlinarith⟩
  have hsmall : 10 * (n : ℝ) * 2^n * δ ≤ 10 * n^3 * 4^n * δ := by
    gcongr
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sq_nonneg (n : ℝ))]
  have hres := complementary_frame_residual_le U V hU hV hrank x
    (show 0 ≤ 10 * (n : ℝ) * 4^n * δ by positivity) hcross
  constructor
  · apply le_trans hres
    apply le_trans _ hbudget
    calc
      _ ≤ 10 * (n:ℝ)^3 * 4^n * δ + 2 * n * (10 * n * 4^n * δ) * n :=
        add_le_add (hQx.trans hsmall) (mul_le_mul_of_nonneg_left hxN (by positivity))
      _ = _ := by ring
  · apply (hPy.trans hsmall).trans
    apply le_trans _ hbudget
    gcongr
    norm_num

/-- The Gram projection of a row matrix. Over the rationals every entry of
this formula is rational, including the empty-matrix case. -/
noncomputable def rowGramProjector {K : Type*} [Field K] (D : Matrix (Fin r) (Fin n) K) :
    Matrix (Fin n) (Fin n) K := Dᵀ * (D * Dᵀ)⁻¹ * D

/-- The row independence needed by the algorithm makes the Gram matrix invertible. -/
theorem gram_det_isUnit_of_independent_rows {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (D : Matrix (Fin r) (Fin n) K) (h : LinearIndependent K D.row) :
    IsUnit (D * Dᵀ).det := by
  have hker : LinearMap.ker Dᵀ.mulVecLin = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    apply Matrix.mulVec_injective_iff.mpr
    simpa only [Matrix.col_transpose] using h
  have hgram : LinearMap.ker (D * Dᵀ).mulVecLin = ⊥ :=
    (by simpa only [Matrix.transpose_transpose] using
      (Matrix.ker_mulVecLin_transpose_mul_self Dᵀ).trans hker)
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp (LinearMap.ker_eq_bot.mp hgram))

theorem rowGramProjector_transpose {K : Type*} [Field K] (D : Matrix (Fin r) (Fin n) K) :
    (rowGramProjector D)ᵀ = rowGramProjector D := by
  simp [rowGramProjector, Matrix.transpose_nonsing_inv, Matrix.mul_assoc]

theorem rowGramProjector_fix_rows {K : Type*} [Field K] (D : Matrix (Fin r) (Fin n) K)
    (h : IsUnit (D * Dᵀ).det) : rowGramProjector D * Dᵀ = Dᵀ := by
  unfold rowGramProjector
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.mul_one]

theorem rowGramProjector_idempotent {K : Type*} [Field K] (D : Matrix (Fin r) (Fin n) K)
    (h : IsUnit (D * Dᵀ).det) : rowGramProjector D * rowGramProjector D = rowGramProjector D := by
  calc
    _ = ((rowGramProjector D * Dᵀ) * (D * Dᵀ)⁻¹) * D := by simp [rowGramProjector, Matrix.mul_assoc]
    _ = _ := by rw [rowGramProjector_fix_rows D h]; rfl

/-- A vector is fixed by the Gram projection exactly if it is a linear
combination of the original rows. -/
theorem rowGramProjector_fix_iff {K : Type*} [Field K] (D : Matrix (Fin r) (Fin n) K)
    (h : IsUnit (D * Dᵀ).det) (x : Fin n → K) :
    rowGramProjector D *ᵥ x = x ↔ ∃ c, Dᵀ *ᵥ c = x := by
  constructor
  · intro hx
    refine ⟨(D * Dᵀ)⁻¹ *ᵥ (D *ᵥ x), ?_⟩
    simpa only [rowGramProjector, ← Matrix.mulVec_mulVec] using hx
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_mulVec, rowGramProjector_fix_rows D h]

/-- The trace of the rational Gram projection is exactly the row count. -/
theorem rowGramProjector_trace {K : Type*} [Field K] (D : Matrix (Fin r) (Fin n) K)
    (h : IsUnit (D * Dᵀ).det) : (rowGramProjector D).trace = r := by
  rw [rowGramProjector, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ h,
    Matrix.trace_one, Fintype.card_fin]

/-- Symmetric idempotents are determined by their fixed subspace. -/
theorem projector_eq_of_fix_iff {K : Type*} [Field K] (P Q : Matrix (Fin n) (Fin n) K)
    (hPt : Pᵀ = P) (hQt : Qᵀ = Q) (hP : P * P = P) (hQ : Q * Q = Q)
    (hfix : ∀ x, P *ᵥ x = x ↔ Q *ᵥ x = x) : P = Q := by
  have hPQ : P * Q = Q := by
    apply Matrix.mulVec_injective; funext x
    rw [← Matrix.mulVec_mulVec]
    apply (hfix _).mpr
    rw [Matrix.mulVec_mulVec, hQ]
  have hQP : Q * P = P := by
    apply Matrix.mulVec_injective; funext x
    rw [← Matrix.mulVec_mulVec]
    apply (hfix _).mp
    rw [Matrix.mulVec_mulVec, hP]
  have ht := congrArg Matrix.transpose hQP
  simpa only [Matrix.transpose_mul, hPt, hQt, hPQ] using ht.symm

/-- Gram projections and an orthonormal basis with the same column span give
the same matrix. -/
theorem rowGramProjector_eq_frame (D : Matrix (Fin r) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin r) ℝ) (hD : LinearIndependent ℝ D.row)
    (hU : Uᵀ * U = 1)
    (hspan : Submodule.span ℝ (Set.range D.row) = Submodule.span ℝ (Set.range U.col)) :
    rowGramProjector D = U * Uᵀ := by
  have hg := gram_det_isUnit_of_independent_rows D hD
  obtain ⟨hUt, hUi, _⟩ := frame_projector_properties U hU
  apply projector_eq_of_fix_iff _ _ (rowGramProjector_transpose D) hUt
    (rowGramProjector_idempotent D hg) hUi
  intro x
  rw [rowGramProjector_fix_iff D hg]
  have hmem : (∃ c, Dᵀ *ᵥ c = x) ↔ ∃ c, U *ᵥ c = x := by
    change x ∈ LinearMap.range Dᵀ.mulVecLin ↔ x ∈ LinearMap.range U.mulVecLin
    simp only [Matrix.range_mulVecLin, Matrix.col_transpose, hspan]
  rw [hmem]
  constructor
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hU, Matrix.mul_one]
  · intro hx
    exact ⟨Uᵀ *ᵥ x, (Matrix.mulVec_mulVec x U Uᵀ).trans hx⟩

/-- Construct orthonormal frame columns for the rounded row space by Gram–Schmidt. -/
theorem exists_orthonormal_frame_of_rows (D : Matrix (Fin r) (Fin n) ℝ)
    (hD : LinearIndependent ℝ D.row) :
    ∃ U : Matrix (Fin n) (Fin r) ℝ, Uᵀ * U = 1 ∧
      Submodule.span ℝ (Set.range D.row) = Submodule.span ℝ (Set.range U.col) ∧
      rowGramProjector D = U * Uᵀ := by
  let e : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := (WithLp.linearEquiv 2 ℝ _).symm
  let v := e ∘ D.row
  let u := gramSchmidtNormed ℝ v
  have hv : LinearIndependent ℝ v := hD.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  have hu : Orthonormal ℝ u := gramSchmidtNormed_orthonormal hv
  let U : Matrix (Fin n) (Fin r) ℝ := fun i j => u j i
  have hU : Uᵀ * U = 1 := by
    ext i j
    have hinner := orthonormal_iff_ite.mp hu j i
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hinner
    change (∑ k, u i k * u j k) = (1 : Matrix (Fin r) (Fin r) ℝ) i j
    rw [Matrix.one_apply]
    have heq : (j = i) = (i = j) := propext eq_comm
    simpa [dotProduct, heq] using hinner
  have hspan : Submodule.span ℝ (Set.range D.row) = Submodule.span ℝ (Set.range U.col) := by
    have hh := (span_gramSchmidtNormed_range (𝕜 := ℝ) v).trans (span_gramSchmidt ℝ v)
    have hm := congrArg (Submodule.map e.symm.toLinearMap) hh.symm
    simp only [Submodule.map_span, ← Set.range_comp] at hm
    exact hm
  exact ⟨U, hU, hspan, rowGramProjector_eq_frame D U hD hU hspan⟩

/-- Field embeddings commute with the Gram projector. In particular the
projector computed over the input rationals acts as the real projection. -/
theorem rowGramProjector_map {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (D : Matrix (Fin r) (Fin n) K) :
    (rowGramProjector D).map f = rowGramProjector (D.map f) := by
  have hi (A : Matrix (Fin r) (Fin r) K) : A⁻¹.map f = (A.map f)⁻¹ := by
    rw [Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv, Ring.inverse_eq_inv]
    ext i j
    change f (A.det⁻¹ * A.adjugate i j) = (A.map f).det⁻¹ * (A.map f).adjugate i j
    rw [map_mul, map_inv₀, f.map_det]
    exact congrArg (fun z => (f.mapMatrix A).det⁻¹ * z) (congrFun (congrFun (f.map_adjugate A) i) j)
  simp only [rowGramProjector, Matrix.map_mul, Matrix.transpose_map, hi]

/-- The absolute row correlations of y propagate linearly with the coefficient
one-norm. This is the testing step for the triangular bases. -/
theorem row_combination_dot_bound (D : Matrix (Fin r) (Fin n) ℝ) (c : Fin r → ℝ)
    (y : Fin n → ℝ) {ε : ℝ} (hrows : ∀ i, |D.row i ⬝ᵥ y| ≤ ε) :
    |(Dᵀ *ᵥ c) ⬝ᵥ y| ≤ (∑ i, |c i|) * ε := by
  rw [dotProduct_comm (Dᵀ *ᵥ c) y, Matrix.dotProduct_transpose_mulVec]
  change |∑ i, c i * (D.row i ⬝ᵥ y)| ≤ _
  calc
    _ ≤ ∑ i, |c i * (D.row i ⬝ᵥ y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |c i| * ε := Finset.sum_le_sum fun i _ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hrows i) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

/-- The symmetric projector's Euclidean test implemented from row correlations
and bounded triangular coordinates in its unit sphere. -/
theorem rowGramProjector_mulVec_le_of_row_test (D : Matrix (Fin r) (Fin n) ℝ)
    (hD : LinearIndependent ℝ D.row) (y : Fin n → ℝ) {ε L : ℝ} (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hrows : ∀ i, |D.row i ⬝ᵥ y| ≤ ε)
    (hrepr : ∀ c : Fin r → ℝ, coordinateNorm (Dᵀ *ᵥ c) = 1 → ∑ i, |c i| ≤ L) :
    coordinateNorm (rowGramProjector D *ᵥ y) ≤ L * ε := by
  have hg := gram_det_isUnit_of_independent_rows D hD
  apply coordinateNorm_projector_le_of_unit_test _ (rowGramProjector_transpose D)
    (rowGramProjector_idempotent D hg) _ (mul_nonneg hL hε)
  intro w hw hnorm
  obtain ⟨c, rfl⟩ := (rowGramProjector_fix_iff D hg w).mp hw
  exact (row_combination_dot_bound D c y hrows).trans
    (mul_le_mul_of_nonneg_right (hrepr c hnorm) hε)

private theorem frame_column_unit (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (i : Fin r) : coordinateNorm (U.col i) = 1 := by
  have hsq : coordinateNorm (U.col i) ^ 2 = 1 := by
    rw [coordinateNorm_sq]
    simpa [Matrix.col, Matrix.mul_apply, sq] using congrFun (congrFun hU i) i
  have hnn : 0 ≤ coordinateNorm (U.col i) := norm_nonneg _
  nlinarith

private theorem frame_column_rep (D : Matrix (Fin r) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin r) ℝ)
    (hspan : Submodule.span ℝ (Set.range D.row) = Submodule.span ℝ (Set.range U.col))
    (i : Fin r) : ∃ c, Dᵀ *ᵥ c = U.col i := by
  change U.col i ∈ LinearMap.range Dᵀ.mulVecLin
  rw [Matrix.range_mulVecLin, Matrix.col_transpose, hspan]
  exact Submodule.subset_span (Set.mem_range_self i)

/-- Correlations between arbitrary orthonormal frame columns from the two
rounded systems, using just the bounded row correlations and one-norm
estimates for coefficients of unit vectors. -/
theorem cross_frame_bound_of_rows
    (D : Matrix (Fin r) (Fin n) ℝ) (E : Matrix (Fin s) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin r) ℝ) (V : Matrix (Fin n) (Fin s) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hsD : Submodule.span ℝ (Set.range D.row) = Submodule.span ℝ (Set.range U.col))
    (hsE : Submodule.span ℝ (Set.range E.row) = Submodule.span ℝ (Set.range V.col))
    {ε L : ℝ} (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hrows : ∀ i j, |D.row i ⬝ᵥ E.row j| ≤ ε)
    (hD : ∀ c : Fin r → ℝ, coordinateNorm (Dᵀ *ᵥ c) = 1 → ∑ i, |c i| ≤ L)
    (hE : ∀ c : Fin s → ℝ, coordinateNorm (Eᵀ *ᵥ c) = 1 → ∑ i, |c i| ≤ L)
    (i : Fin r) (j : Fin s) : |(Uᵀ * V) i j| ≤ L * (L * ε) := by
  obtain ⟨c, hc⟩ := frame_column_rep D U hsD i
  obtain ⟨d, hd⟩ := frame_column_rep E V hsE j
  have hcn := hD c (hc ▸ frame_column_unit U hU i)
  have hdn := hE d (hd ▸ frame_column_unit V hV j)
  have hrow k : |D.row k ⬝ᵥ V.col j| ≤ L * ε := by
    rw [dotProduct_comm, ← hd]
    apply (row_combination_dot_bound E d (D.row k) fun l => ?_).trans
      (mul_le_mul_of_nonneg_right hdn hε)
    rw [dotProduct_comm]
    exact hrows k l
  change |U.col i ⬝ᵥ V.col j| ≤ _
  rw [← hc]
  exact (row_combination_dot_bound D c (V.col j) hrow).trans
    (mul_le_mul_of_nonneg_right hcn (mul_nonneg hL hε))

/-- The residual estimates (2.5) for the matrices actually returned by the
Gram formula. The variable ε in the correlation proof has already absorbed
the rounding error on either or both rows. -/
theorem rounded_projector_estimates
    (D : Matrix (Fin r) (Fin n) ℝ) (E : Matrix (Fin s) (Fin n) ℝ)
    (hD : LinearIndependent ℝ D.row) (hE : LinearIndependent ℝ E.row)
    (hrank : r + s = n) (hn : 0 < n) (δ : ℝ) (hδ : 0 ≤ δ)
    (hbudget : 30 * (n : ℝ)^3 * 4^n * δ ≤ 1 / (2000 * n))
    (x y : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 1)
    (hrows : ∀ i j, |D.row i ⬝ᵥ E.row j| ≤ 10 * n * δ)
    (hyD : ∀ i, |D.row i ⬝ᵥ y| ≤ 10 * n * δ)
    (hxE : ∀ i, |E.row i ⬝ᵥ x| ≤ 10 * n * δ)
    (hrepD : ∀ c : Fin r → ℝ, coordinateNorm (Dᵀ *ᵥ c) = 1 → ∑ i, |c i| ≤ 2^n)
    (hrepE : ∀ c : Fin s → ℝ, coordinateNorm (Eᵀ *ᵥ c) = 1 → ∑ i, |c i| ≤ 2^n) :
    coordinateNorm ((1 - rowGramProjector D) *ᵥ x) ≤ 1 / (2000 * n) ∧
    coordinateNorm (rowGramProjector D *ᵥ y) ≤ 1 / (2000 * n) := by
  obtain ⟨U, hU, hsD, hDP⟩ := exists_orthonormal_frame_of_rows D hD
  obtain ⟨V, hV, hsE, hEQ⟩ := exists_orthonormal_frame_of_rows E hE
  have hε : 0 ≤ 10 * (n : ℝ) * δ := by positivity
  have hL : 0 ≤ (2 : ℝ)^n := by positivity
  have hpow : (2 : ℝ)^n * 2^n = 4^n := by rw [← mul_pow]; norm_num
  have hcross := cross_frame_bound_of_rows D E U V hU hV hsD hsE hε hL hrows hrepD hrepE
  have hPy := rowGramProjector_mulVec_le_of_row_test D hD y hε hL hyD hrepD
  have hQx := rowGramProjector_mulVec_le_of_row_test E hE x hε hL hxE hrepE
  rw [hDP] at hPy ⊢
  rw [hEQ] at hQx
  apply geometric_projection_bounds U V hU hV hrank hn x y hx δ hδ hbudget
  · intro i j
    calc
      _ ≤ _ := hcross i j
      _ = (2^n * 2^n) * 10 * n * δ := by ring
      _ = _ := by rw [hpow]; ring
  · linarith only [hQx]
  · linarith only [hPy]

end Geometry
end LinearProgramming
end Optimization
end OAI

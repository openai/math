import OAI.Optimization.LinearProgramming.Geometry.Hidden
import OAI.Optimization.LinearProgramming.Geometry.Projection

/-! Base change for the row-space alternative and its determinant circuits. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix Submodule
open scoped Matrix BigOperators

variable {n r s k : ℕ}

/-- Dot-product orthogonality to a row span is exactly the homogeneous matrix system. -/
theorem rowSpan_orthogonalBilin_eq_ker {K : Type*} [Field K]
    (D : Matrix (Fin r) (Fin n) K) :
    (span K (Set.range D.row)).orthogonalBilin (dotProductBilin K K) = LinearMap.ker D.mulVecLin := by
  ext y
  constructor
  · intro h
    apply LinearMap.mem_ker.mpr
    funext i
    exact h _ (subset_span ⟨i, rfl⟩)
  · intro h x hx
    rw [← range_vecMulLinear] at hx
    obtain ⟨u, rfl⟩ := hx
    change (u ᵥ* D) ⬝ᵥ y = 0
    have hz : D *ᵥ y = 0 := LinearMap.mem_ker.mp h
    rw [← Matrix.dotProduct_mulVec, hz, dotProduct_zero]

/-- Two independent sets of orthogonal rows with complementary cardinalities present the
full orthogonal pair, including when either matrix has no rows. -/
theorem complementary_rowSpan {K : Type*} [Field K]
    (D : Matrix (Fin r) (Fin n) K) (E : Matrix (Fin s) (Fin n) K)
    (hD : LinearIndependent K D.row) (hE : LinearIndependent K E.row)
    (hDE : D * Eᵀ = 0) (hsize : r + s = n) :
    span K (Set.range E.row) = (span K (Set.range D.row)).orthogonalBilin (dotProductBilin K K) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro y hy x hx
    exact rowSpan_dot_eq_zero D E hDE hx hy
  · rw [rowSpan_orthogonalBilin_eq_ker, ← Matrix.rank_eq_finrank_span_row]
    have h := D.mulVecLin.finrank_range_add_finrank_ker
    change D.rank + Module.finrank K (LinearMap.ker D.mulVecLin) = _ at h
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hD.rank_matrix, Fintype.card_fin] at h
    rw [hE.rank_matrix, Fintype.card_fin]
    omega

/-- Full row rank is preserved by an embedding of ordered fields. The Gram determinant
provides a nonsingular witness which commutes with every field homomorphism. -/
theorem independent_rows_map {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Field L] (f : K →+* L) (D : Matrix (Fin r) (Fin n) K) (hD : LinearIndependent K D.row) :
    LinearIndependent L (D.map f).row := by
  let E := D.map f
  have hG := (gram_det_isUnit_of_independent_rows D hD).map f.toMonoidHom
  have hf : (E * Eᵀ).det = f (D * Dᵀ).det := by
    rw [f.map_det]
    change (E * Eᵀ).det = ((D * Dᵀ).map f).det
    rw [Matrix.map_mul]
    rfl
  have hInv : IsUnit (E * Eᵀ) := (Matrix.isUnit_iff_isUnit_det _).mpr (hf.symm ▸ hG)
  apply Matrix.vecMul_injective_iff.mp
  intro u v huv
  apply Matrix.vecMul_injective_of_isUnit hInv
  change u ᵥ* (E * Eᵀ) = v ᵥ* (E * Eᵀ)
  rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
  exact congrArg (fun z => z ᵥ* Eᵀ) huv

/-- Every minor used for a circuit has the same value after interpreting the original
coefficients in the larger field. -/
theorem circuitMinor_map {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (D : Matrix (Fin (k + 1)) (Fin n) K) (J : Fin k → Fin n) (j : Fin n) :
    circuitMinor (D.map f) J j = f (circuitMinor D J j) := (f.map_det _).symm

/-- The coordinate support detected by the real compressed test is already realized by a
rational signed-minor row of the original rational basis. -/
theorem rational_row_witness_iff_real (D : Matrix (Fin r) (Fin n) ℚ)
    (hD : LinearIndependent ℚ D.row) (i : Fin n) :
    (∃ x ∈ span ℚ (Set.range D.row), 0 ≤ x ∧ 0 < x i) ↔
    (∃ y ∈ span ℝ (Set.range (D.map (Rat.castHom ℝ)).row), 0 ≤ y ∧ 0 < y i) := by
  let f := Rat.castHom ℝ
  constructor
  · rintro ⟨x, hx, h0, hi⟩
    refine ⟨f ∘ x, ?_, fun j => ?_, ?_⟩
    · rw [← range_vecMulLinear] at hx ⊢
      obtain ⟨c, rfl⟩ := hx
      exact ⟨f ∘ c, funext fun j => (f.map_vecMul D c j).symm⟩
    · change (0 : ℝ) ≤ (x j : ℝ)
      exact_mod_cast (show (0 : ℚ) ≤ x j from h0 j)
    · change (0 : ℝ) < (x i : ℝ)
      exact_mod_cast hi
  · cases r with
    | zero => simp
    | succ k =>
      rintro ⟨x, hx, hx0, hxi⟩
      obtain ⟨J, _, _, hor⟩ := exists_nonnegative_circuitMinor (D.map f) (independent_rows_map f D hD) i hx hx0 hxi
      have hm := circuitMinor_mem_rowSpan D J
      rcases hor with ⟨hpos, hp⟩ | ⟨hneg, hn⟩
      · refine ⟨circuitMinor D J, hm, fun j => ?_, ?_⟩
        · have h := hpos j
          change (0 : ℝ) ≤ circuitMinor (D.map f) J j at h
          rw [circuitMinor_map] at h
          change (0 : ℚ) ≤ circuitMinor D J j
          change (0 : ℝ) ≤ ((circuitMinor D J j : ℚ) : ℝ) at h
          exact_mod_cast h
        · rw [circuitMinor_map] at hp
          change (0 : ℝ) < ((circuitMinor D J i : ℚ) : ℝ) at hp
          exact_mod_cast hp
      · refine ⟨-circuitMinor D J, Submodule.neg_mem _ hm, fun j => ?_, ?_⟩
        · have h := hneg j
          change (0 : ℝ) ≤ -circuitMinor (D.map f) J j at h
          rw [circuitMinor_map] at h
          change (0 : ℚ) ≤ -circuitMinor D J j
          change (0 : ℝ) ≤ -((circuitMinor D J j : ℚ) : ℝ) at h
          exact_mod_cast h
        · rw [circuitMinor_map] at hn
          change (0 : ℚ) < -circuitMinor D J i
          change (0 : ℝ) < -((circuitMinor D J i : ℚ) : ℝ) at hn
          exact_mod_cast hn

end Geometry
end LinearProgramming
end Optimization
end OAI

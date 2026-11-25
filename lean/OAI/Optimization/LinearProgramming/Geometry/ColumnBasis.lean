import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Selecting a nonsingular bordered minor through the designated coordinate. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix Submodule
open scoped Matrix

/-- When the rows restricted to the zero coordinates and `i` distinguish all coefficients,
there are `k` distinct zero coordinates which, together with `i`, give a nonsingular minor. -/
theorem exists_circuit_columns {K ι : Type*} [Field K] [Fintype ι] {k : ℕ}
    (D : Matrix (Fin (k + 1)) ι K) (i : ι) (x : ι → K)
    (hx : x ∈ span K (Set.range D.row)) (hxi : x i ≠ 0)
    (hker : ∀ u : Fin (k + 1) → K, (u ᵥ* D) i = 0 →
      (∀ j, x j = 0 → (u ᵥ* D) j = 0) → u = 0) :
    ∃ J : Fin k → ι, Function.Injective J ∧ (∀ q, x (J q) = 0) ∧
      (D.submatrix id (Fin.lastCases i J)).det ≠ 0 := by
  classical
  let T : Set ι := {j | j = i ∨ x j = 0}
  have hi : i ∈ T := Or.inl rfl
  let A := D.submatrix id (Subtype.val : T → ι)
  have hA : Function.Injective A.vecMul := by
    change Function.Injective A.vecMulLinear
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro u hu
    exact hker u (congrFun hu ⟨i, hi⟩) fun j hj => congrFun hu ⟨j, Or.inr hj⟩
  have himage (s : Set ι) : Set.range (fun j : s => D.col j.val) = D.col '' s := by
    ext v
    simp
  have hT : span K (D.col '' T) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := ((Matrix.vecMul_injective_iff.mp hA).rank_matrix)
    rw [A.rank_eq_finrank_span_cols] at h
    change Module.finrank K (span K (Set.range (fun j : T => D.col j.val))) = _ at h
    rw [← himage T, Module.finrank_fintype_fun_eq_card]
    exact h
  have hcol : D.col i ≠ 0 := by
    obtain ⟨w, hw⟩ := (show x ∈ LinearMap.range D.vecMulLinear by rwa [range_vecMulLinear])
    intro h
    apply hxi
    rw [← hw]
    change w ⬝ᵥ D.col i = 0
    rw [h, dotProduct_zero]
  have hli : LinearIndepOn K D.col {i} := (linearIndepOn_singleton_iff K).mpr hcol
  have hsub : {i} ⊆ T := Set.singleton_subset_iff.mpr hi
  let B := hli.extend hsub
  have hB : LinearIndepOn K D.col B := hli.linearIndepOn_extend hsub
  have hBspan : span K (D.col '' B) = ⊤ := (hli.span_image_extend_eq_span_image hsub).trans hT
  have hcard : Fintype.card B = k + 1 := by
    have h := finrank_span_eq_card hB.linearIndependent
    rw [himage, hBspan] at h
    simpa using h.symm
  let b : B := ⟨i, hli.subset_extend hsub (Set.mem_singleton i)⟩
  let e : Fin (k + 1) ≃ B := (Fintype.equivFinOfCardEq hcard).symm
  let p := e.trans (Equiv.swap (e (Fin.last k)) b)
  have hlast : p (Fin.last k) = b := by simp [p]
  let J : Fin k → ι := fun q => (p q.castSucc).val
  have hJ : Fin.lastCases i J = fun q => (p q).val := by
    funext q
    refine Fin.lastCases ?_ (fun j => ?_) q
    · simp [hlast, b]
    · simp [J]
  refine ⟨J, Subtype.val_injective.comp (p.injective.comp (Fin.castSucc_injective k)), ?_, ?_⟩
  · intro q
    rcases hli.extend_subset hsub (p q.castSucc).property with he | he
    · have hsame : p q.castSucc = p (Fin.last k) := by rw [hlast]; exact Subtype.ext he
      exact (Fin.ne_of_lt (Fin.castSucc_lt_last q) (p.injective hsame)).elim
    · exact he
  · apply IsUnit.ne_zero
    apply (Matrix.isUnit_iff_isUnit_det _).mp
    apply Matrix.linearIndependent_cols_iff_isUnit.mp
    rw [hJ]
    exact hB.linearIndependent.comp p p.injective

/-- The pivot selection in the triangular system always has a candidate: an invertible
old prefix extends by one column when the next prefix retains independent rows. -/
theorem exists_nonsingular_column_extension {K ι : Type*} [Field K] [Fintype ι] {k : ℕ}
    (D : Matrix (Fin (k + 1)) ι K) (J : Fin k → ι) (hD : LinearIndependent K D.row)
    (hJ : (D.submatrix Fin.castSucc J).det ≠ 0) :
    ∃ j : ι, j ∉ Set.range J ∧ (D.submatrix id (Fin.lastCases j J)).det ≠ 0 := by
  classical
  let v := D.col ∘ J
  have hv : LinearIndependent K v := by
    let restrictRows : (Fin (k + 1) → K) →ₗ[K] (Fin k → K) :=
      LinearMap.pi fun r => LinearMap.proj r.castSucc
    apply LinearIndependent.of_comp restrictRows
    exact Matrix.linearIndependent_cols_of_det_ne_zero hJ
  have hspan : span K (Set.range D.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← D.rank_eq_finrank_span_cols, hD.rank_matrix, Module.finrank_fintype_fun_eq_card]
  have hproper : span K (Set.range v) ≠ ⊤ := by
    intro ht
    have h := finrank_span_eq_card hv
    rw [ht] at h
    simp at h
  obtain ⟨j, hj⟩ : ∃ j, D.col j ∉ span K (Set.range v) := by
    by_contra! h
    apply hproper
    apply top_unique
    rw [← hspan]
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr h)
  refine ⟨j, ?_, ?_⟩
  · rintro ⟨q, rfl⟩
    exact hj (Submodule.subset_span (Set.mem_range_self q))
  · have hs : (D.submatrix id (Fin.lastCases j J)).col = Fin.snoc v (D.col j) := by
      funext q
      refine Fin.lastCases ?_ (fun r => ?_) q
      · funext a
        simp [Matrix.col, Matrix.submatrix]
      · funext a
        simp [Matrix.col, Matrix.submatrix, v, Function.comp_def]
    apply IsUnit.ne_zero
    apply (Matrix.isUnit_iff_isUnit_det _).mp
    apply Matrix.linearIndependent_cols_iff_isUnit.mp
    rw [hs]
    exact linearIndependent_finSnoc.mpr ⟨hv, hj⟩

end Geometry
end LinearProgramming
end Optimization
end OAI

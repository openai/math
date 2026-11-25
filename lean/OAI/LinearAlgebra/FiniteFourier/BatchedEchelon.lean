import OAI.LinearAlgebra.FiniteFourier.BatchedQuotient
import Mathlib.LinearAlgebra.Projection

/-! # Echelon representatives of a shared row quotient -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Module LinearMap Matrix
open scoped Classical
noncomputable section

private theorem exists_pivot_lift {K W V : Type*} [Field K] [AddCommGroup W] [Module K W]
    [AddCommGroup V] [Module K V] (f : ℕ → W →ₗ[K] V) (t : ℕ) :
    ∃ g : V →ₗ[K] W, (∀ x j, j < t → f j (g x) = 0) ∧
      LinearMap.range ((f t).comp g) = blockPivots f t := by
  let L := blockKernel f t
  let h := (f t).domRestrict L
  obtain ⟨s, hs⟩ := h.rangeRestrict.exists_rightInverse_of_surjective h.range_rangeRestrict
  obtain ⟨N, hN⟩ := Submodule.exists_isCompl (LinearMap.range h)
  let p := (LinearMap.range h).projectionOnto N hN
  let g := L.subtype.comp (s.comp p)
  refine ⟨g, fun x => (mem_blockKernel_iff f t _).mp (s (p x)).property, ?_⟩
  have he : LinearMap.range h = blockPivots f t := LinearMap.range_domRestrict ..
  rw [← he]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨s (p x), rfl⟩
  · intro y hy
    refine ⟨y, ?_⟩
    change h (s ((LinearMap.range h).projectionOnto N hN y)) = y
    rw [Submodule.projectionOnto_apply_of_mem_left hN hy]
    exact congrArg Subtype.val (LinearMap.congr_fun hs ⟨y, hy⟩)

variable {K : Type*} [Field K] {R : Type} [Fintype R] {J : ℕ}

theorem exists_echelon_left_factor (Q : Matrix (R × Fin J) (R × Fin J) K) :
    ∃ L : Matrix (R × Fin J) (R × Fin J) K,
      (∀ (a b : R) (i j : Fin J), j < i → (L * Q) (a,i) (b,j) = 0) ∧
      (∑ i : Fin J, ((L * Q).submatrix (fun a => (a,i)) (fun b => (b,i))).rank) = Q.rank := by
  let W := LinearMap.range Q.transpose.mulVecLin
  let f (t : ℕ) : W →ₗ[K] (R → K) :=
    if ht : t < J then
      { toFun := fun w a => w.val (a, ⟨t, ht⟩)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    else 0
  have hf (i : Fin J) (w : W) (a : R) : f i.val w a = w.val (a,i) := by
    simp [f, i.isLt]
  choose g hgzero hgrange using fun i : Fin J => exists_pivot_lift f i.val
  let row (a : R) (i : Fin J) := g i (Pi.single a 1)
  choose coeff hcoeff using fun (a : R) (i : Fin J) => (row a i).property
  let L : Matrix (R × Fin J) (R × Fin J) K := fun ai => coeff ai.1 ai.2
  have hentry (a : R) (i : Fin J) (b : R) (j : Fin J) :
      (L * Q) (a,i) (b,j) = f j.val (row a i) b := by
    rw [hf, ← hcoeff a i]
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_transpose]
    rfl
  refine ⟨L, ?_, ?_⟩
  · intro a b i j hji
    rw [hentry]
    exact congrFun (hgzero i (Pi.single a 1) j.val hji) b
  · have hr (i : Fin J) :
        ((L * Q).submatrix (fun a => (a,i)) (fun b => (b,i))).rank =
          finrank K (blockPivots f i.val) := by
      let H := (L * Q).submatrix (fun a => (a,i)) (fun b => (b,i))
      have he : H.transpose.mulVecLin = (f i.val).comp (g i) := by
        apply (Pi.basisFun K R).ext
        intro a
        funext b
        rw [Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
        exact hentry a i b i
      change H.rank = _
      rw [← Matrix.rank_transpose, Matrix.rank, he, hgrange]
    have sep (w : W) (hw : ∀ j < J, f j w = 0) : w = 0 := by
      apply Subtype.ext
      funext ⟨a,i⟩
      exact (hf i w a).symm.trans (congrFun (hw i.val i.isLt) a)
    simp_rw [hr]
    rw [Fin.sum_univ_eq_sum_range (fun t => finrank K (blockPivots f t)),
      sum_blockPivots_finrank_of_separating f J sep, ← Matrix.rank_transpose Q]
    rfl

end
end FiniteFourier
end LinearAlgebra
end OAI

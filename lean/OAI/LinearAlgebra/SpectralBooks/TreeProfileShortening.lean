import OAI.LinearAlgebra.SpectralBooks.FinitePlaneCriterion
import OAI.LinearAlgebra.SpectralBooks.SpectralAxisExtension

/-! # Profile shortening in the tree case

The four corners of a unit square violate the tree four-point inequality.
The diagonal normalization transfers this strict inequality to a single
finite spectral point. Consequently the tree case lacks a spectral plane
and gives a profile shortening of the two-dimensional crossing.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open SiteTensor

noncomputable section

/-- A square of a spectral plane gives a finite non-tree wire metric over the same field. -/
theorem hasNonTreeWireMetric_of_spectralPlane {K : Type*} [Field K]
    (P : SpectralPlacementPrices K (EuclideanSpace ℝ (Fin 2))) : HasNonTreeWireMetric K := by
  let p : Fin 2 × Fin 2 ↪ EuclideanSpace ℝ (Fin 2) :=
    ⟨fun x ↦ WithLp.toLp 2 ![(x.1 : ℝ), (x.2 : ℝ)], by
      intro x y h
      apply Prod.ext <;> apply Fin.ext
      · have hx : (x.1 : ℝ) = (y.1 : ℝ) := congrArg (fun z : EuclideanSpace ℝ (Fin 2) ↦ z 0) h
        exact_mod_cast hx
      · have hx : (x.2 : ℝ) = (y.2 : ℝ) := congrArg (fun z : EuclideanSpace ℝ (Fin 2) ↦ z 1) h
        exact_mod_cast hx⟩
  obtain ⟨φ, hpos, hprice⟩ := P.normalized_group p
  let c := P.price (Raw.diagonal (Fin 2 × Fin 2) K (Fin 2)) p
  have hc : 0 < c := hpos
  let W := Raw.diagonal (Fin 2) K (Fin 2)
  have hW : W.coeff ≠ 0 := by
    intro h
    have h0 := congrFun h (fun _ ↦ (0 : Fin 2))
    change (Raw.diagonal (Fin 2) K (Fin 2)).coeff (fun _ ↦ (0 : Fin 2)) = (0 : K) at h0
    rw [Raw.diagonal_coeff_at (0 : Fin 2)] at h0
    simp at h0
  have hdist (i j : Fin 2 × Fin 2) : c * rawWireDistance φ 1 i j = dist (p i) (p j) := by
    have h := (hprice ![i, j] W hW).symm.trans (P.wire (p ∘ ![i, j]))
    simpa only [rawWireDistance, rawLogPrice, one_mul, c, W, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h
  refine ⟨Fin 2 × Fin 2, inferInstance, inferInstance, φ, (0, 0), (1, 1), (0, 1), (1, 0), ?_⟩
  dsimp only
  apply (mul_lt_mul_iff_of_pos_left hc).mp
  rw [mul_max_of_nonneg _ _ hc.le]
  simp only [mul_add, hdist, EuclideanSpace.dist_eq, Fin.sum_univ_two]
  have hx (i : Fin 2 × Fin 2) : (p i).ofLp 0 = (i.1 : ℝ) := rfl
  have hy (i : Fin 2 × Fin 2) : (p i).ofLp 1 = (i.2 : ℝ) := rfl
  norm_num [hx, hy, Real.dist_eq]
  nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]

/-- A field with exclusively tree wire metrics admits profile shortening in dimension two. -/
theorem hasProfileShortening_of_tree {K : Type*} [Field K] (tree : ¬ HasNonTreeWireMetric K) :
    Crossing.HasProfileShortening K 2 := by
  obtain ⟨m, hm, h⟩ := shortenedCrossing_of_no_flat K (D := 2) (by norm_num)
    (hasSpectralAxisExtensions_of_curvature K (fun _ _ _ P hg ↦ P.catZero hg) 2)
    (fun ⟨P⟩ ↦ tree (hasNonTreeWireMetric_of_spectralPlane P))
  exact h.hasProfileShortening (by norm_num) hm

end

end SpectralBooks
end LinearAlgebra
end OAI

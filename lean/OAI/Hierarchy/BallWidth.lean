import OAI.Hierarchy.FlatPrices
import OAI.LinearAlgebra.SpectralBooks.SpectralFlatLaw
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

namespace OAI
/-! # A dimension-independent diagonal upper bound for finitely many unit-ball sites -/

noncomputable section
open scoped Classical BigOperators InnerProductSpace
open LinearAlgebra.SpectralBooks MeasureTheory ProbabilityTheory

namespace Hierarchy.HomogeneousFlat

variable {d : ℕ} {F : Type*} [Field F]

/-- Joint convexity of the placed tensor price is precisely the synchronized
convexity of the diagonal finite-set price. -/
theorem diagonal_eq_meanWidth (P : HomogeneousFlat F d) (S : Finset (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) :
    P.prices.diagonal S = meanWidth S hS := by
  let : DecidableEq (EuclideanSpace ℝ (Fin d)) := Classical.decEq (EuclideanSpace ℝ (Fin d))
  apply flatDiagonalLaw (C := Set.univ) _ convex_univ S hS (Set.subset_univ _)
  refine ⟨P.prices.diagonal_mono,P.prices.intersectingSubmodular,?_,
    fun a _ b _ => P.prices.diagonal_pair a b,
    fun a _ b _ c _ => P.prices.diagonal_triangle_le_half_perimeter a b c⟩
  intro A hA _ a b ha hb hab
  let : Nonempty A := hA.to_subtype
  let x (v : A) := v.val.1
  let y (v : A) := v.val.2
  have H := (P.convex (SiteTensor.Raw.diagonal A F (Fin 2))).2
    (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  have image (f : (EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d))) : Finset.univ.image (fun i : A => f i.val) = A.image f := by
    ext v
    simp
  have comb : a • x + b • y = (fun v : A => a • v.val.1 + b • v.val.2) := rfl
  simpa only [comb, P.prices.price_binaryDiagonal_eq, smul_eq_mul, x, y,
    image (fun v => a • v.1 + b • v.2), image Prod.fst, image Prod.snd] using H

private theorem inner_sq_integral (y : (EuclideanSpace ℝ (Fin d))) :
    Integrable (fun u : (EuclideanSpace ℝ (Fin d)) => ⟪u,y⟫_ℝ^2) (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      (∫ u : (EuclideanSpace ℝ (Fin d)), ⟪u,y⟫_ℝ^2 ∂stdGaussian (EuclideanSpace ℝ (Fin d))) = ‖y‖^2 := by
  let L := innerSL ℝ y
  have hm := IsGaussian.memLp_dual (stdGaussian (EuclideanSpace ℝ (Fin d))) L 2 (by norm_num)
  have vv := variance_dual_stdGaussian L
  rw [variance_eq_integral L.continuous.aemeasurable, integral_strongDual_stdGaussian] at vv
  simpa only [L, sub_zero, innerSL_apply_apply, real_inner_comm y, innerSL_apply_norm] using
    And.intro hm.integrable_sq vv

/-- Each projection of the standard Gaussian has variance at most one. A quadratic
upper bound on the maximum of the projections costs only the square root of the
number of sites. -/
theorem meanWidth_image_le_sqrt_card {J : Type} [Fintype J] [Nonempty J]
    (y : J → (EuclideanSpace ℝ (Fin d))) (hy : ∀ j, ‖y j‖ ≤ 1) :
    meanWidth (Finset.univ.image y) (Finset.univ_nonempty.image _) ≤
      Real.sqrt (2 * Real.pi) * Real.sqrt (Fintype.card J : ℝ) := by
  let S := Finset.univ.image y
  have hS : S.Nonempty := Finset.univ_nonempty.image _
  let a := Real.sqrt (Fintype.card J : ℝ)
  have ha : 0 < a := Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos)
  have hasq : a^2 = Fintype.card J := Real.sq_sqrt (Nat.cast_nonneg _)
  let proj (j : J) (u : (EuclideanSpace ℝ (Fin d))) := ⟪u,y j⟫_ℝ^2
  have hi (j : J) : Integrable (proj j) (stdGaussian (EuclideanSpace ℝ (Fin d))) := (inner_sq_integral (y j)).1
  have hs := integrable_finsetSum Finset.univ (fun j _ => hi j)
  have hs2 : (∫ u : (EuclideanSpace ℝ (Fin d)), ∑ j, proj j u ∂stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ Fintype.card J := by
    rw [integral_finsetSum _ (fun j _ => hi j)]
    calc
      _ ≤ ∑ _j : J, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [(inner_sq_integral (y j)).2]
        nlinarith [norm_nonneg (y j), hy j, sq_nonneg (1-‖y j‖),
          mul_nonneg (sub_nonneg.mpr (hy j)) (by positivity : 0 ≤ 1+‖y j‖)]
      _ = _ := by simp
  have bound (u : (EuclideanSpace ℝ (Fin d))) : (2*a) * support S hS u ≤ a^2 + ∑ j, proj j u := by
    obtain ⟨v,hv,hv'⟩ := Finset.exists_mem_eq_sup' hS (fun x => ⟪u,x⟫_ℝ)
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    change (2*a) * S.sup' hS (fun x => ⟪u,x⟫_ℝ) ≤ _
    rw [hv']
    have hle : proj j u ≤ ∑ k, proj k u :=
      Finset.single_le_sum (fun k _ => sq_nonneg ⟪u,y k⟫_ℝ) (Finset.mem_univ j)
    dsimp only [proj] at hle
    nlinarith only [sq_nonneg (a-⟪u,y j⟫_ℝ), hle]
  have hb := integral_mono ((integrable_support S hS).const_mul (2*a))
    ((integrable_const (a^2)).add hs) bound
  simp only [Pi.add_apply] at hb
  rw [integral_const_mul,integral_add (integrable_const (a^2)) hs,integral_const] at hb
  simp only [probReal_univ,one_smul] at hb
  have havg : (∫ u, support S hS u ∂stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ a := by
    apply (mul_le_mul_iff_right₀ (mul_pos (by norm_num : (0:ℝ) < 2) ha)).mp
    nlinarith only [hasq,hs2,hb]
  exact mul_le_mul_of_nonneg_left havg (Real.sqrt_nonneg _)

/-- Qualitative graph lower bounds use this upper bound on their terminal and block sites. -/
theorem diagonal_image_le_sqrt_card (P : HomogeneousFlat F d)
    {J : Type} [Fintype J] [Nonempty J] (y : J → (EuclideanSpace ℝ (Fin d))) (hy : ∀ j, ‖y j‖ ≤ 1) :
    P.prices.diagonal (Finset.univ.image y) ≤
      Real.sqrt (2 * Real.pi) * Real.sqrt (Fintype.card J : ℝ) := by
  rw [P.diagonal_eq_meanWidth _ (Finset.univ_nonempty.image _)]
  exact meanWidth_image_le_sqrt_card y hy

/-- The same Gaussian bound on the price of the binary tensor before identifying
repeated entries of the placement. -/
theorem binary_price_le_sqrt_card (P : HomogeneousFlat F d)
    {J : Type} [Fintype J] [Nonempty J] (y : J → (EuclideanSpace ℝ (Fin d))) (hy : ∀ j, ‖y j‖ ≤ 1) :
    P.prices.price (SiteTensor.Raw.diagonal J F (Fin 2)) y ≤
      Real.sqrt (2 * Real.pi) * Real.sqrt (Fintype.card J : ℝ) := by
  rw [P.prices.price_binaryDiagonal_eq]
  convert! P.diagonal_image_le_sqrt_card y hy using 1
  congr 1
  ext
  simp

end Hierarchy.HomogeneousFlat

end
end OAI

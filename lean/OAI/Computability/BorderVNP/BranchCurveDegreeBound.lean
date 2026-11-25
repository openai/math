import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Extension degree from coordinate eliminants

The function field of a branch is generated over the parameter field by its
coordinates. Each coordinate has degree at most the degree of its nonzero
eliminant in the coordinate variable. Taking composita gives a product bound
without any assumption of separability or independence among the coordinates.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open Polynomial

variable {σ F L : Type*} [Field F] [Field L] [Algebra F L] [Fintype σ]

/-- A family of nonzero univariate annihilators of field generators proves
finiteness and bounds the extension degree by the product of their degrees. -/
theorem finrank_le_prod_of_annihilators (x : σ → L) (g : σ → Polynomial F)
    (hgen : IntermediateField.adjoin F (Set.range x) = ⊤) (hne : ∀ i, g i ≠ 0)
    (hroot : ∀ i, aeval (x i) (g i) = 0) :
    FiniteDimensional F L ∧ Module.finrank F L ≤ ∏ i, (g i).natDegree := by
  classical
  have integral (i : σ) : IsIntegral F (x i) :=
    (show IsAlgebraic F (x i) from ⟨g i, hne i, hroot i⟩).isIntegral
  have fin := IntermediateField.finiteDimensional_adjoin (S := Set.range x) (by
    rintro _ ⟨i, rfl⟩
    exact integral i)
  rw [hgen] at fin
  refine ⟨IntermediateField.topEquiv.toLinearEquiv.finiteDimensional, ?_⟩
  have bound (s : Finset σ) :
      Module.finrank F (IntermediateField.adjoin F (x '' (s : Set σ))) ≤ ∏ i ∈ s, (g i).natDegree := by
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.coe_empty, Set.image_empty, IntermediateField.adjoin_empty,
        IntermediateField.finrank_bot, Finset.prod_empty]
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.coe_insert, Set.image_insert_eq, ← Set.singleton_union,
        IntermediateField.adjoin_union]
      refine IntermediateField.finrank_sup_le _ _ |>.trans (Nat.mul_le_mul ?_ ih)
      rw [IntermediateField.adjoin.finrank (integral i)]
      exact natDegree_le_of_dvd (minpoly.dvd F (x i) (hroot i)) (hne i)
  have total := bound Finset.univ
  rwa [Finset.coe_univ, Set.image_univ, hgen, IntermediateField.finrank_top'] at total

/-- For bivariate eliminants over `E[t]`, only their degrees in the outer
coordinate variable enter the extension bound over the rational function field. -/
theorem finrank_le_of_bivariate_eliminants {E : Type*} [Field E]
    [Algebra (FractionRing (Polynomial E)) L] (x : σ → L) (R : σ → Polynomial (Polynomial E))
    (hgen : IntermediateField.adjoin (FractionRing (Polynomial E)) (Set.range x) = ⊤)
    (hne : ∀ i, R i ≠ 0) (hroot : ∀ i,
      aeval (x i) ((R i).map (algebraMap (Polynomial E) (FractionRing (Polynomial E)))) = 0)
    (D : ℕ) (hD : ∀ i, (R i).natDegree ≤ D) :
    FiniteDimensional (FractionRing (Polynomial E)) L ∧
      Module.finrank (FractionRing (Polynomial E)) L ≤ D ^ Fintype.card σ := by
  let f := algebraMap (Polynomial E) (FractionRing (Polynomial E))
  have hinj : Function.Injective f := IsFractionRing.injective _ _
  obtain ⟨fin, bound⟩ := finrank_le_prod_of_annihilators x (fun i => (R i).map f) hgen
    (fun i => (Polynomial.map_ne_zero_iff hinj).mpr (hne i)) hroot
  refine ⟨fin, bound.trans ?_⟩
  calc
    ∏ i, ((R i).map f).natDegree ≤ ∏ _ : σ, D := Finset.prod_le_prod fun i _ =>
      (Polynomial.natDegree_map_le).trans (hD i)
    _ = _ := by simp

end Branch

end BorderVNP
end Computability
end OAI

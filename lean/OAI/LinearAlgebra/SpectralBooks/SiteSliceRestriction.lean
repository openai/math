import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import OAI.LinearAlgebra.SpectralBooks.GroupedSlices
import OAI.LinearAlgebra.SpectralBooks.PermutationStretch
import OAI.LinearAlgebra.SpectralBooks.SliceRestriction

/-!
# Private slice restrictions with individual sites

The common site receives the pair of basis labels. Every matrix at a private
site is an identity, including when its basis indices are multidimensional.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation
open scoped Classical

variable {K S R U I J : Type*} [Field K] [Fintype S] [Fintype R]
  {X : S → Type*} {Y : R → Type*}
  [∀ s, Fintype (X s)] [∀ r, Fintype (Y r)] [Fintype I] [Fintype J]

/-- A matrix at the common site is an ordinary restriction at the full site set. -/
theorem siteRestriction_central_map {V : Type*} [Fintype V]
    (T : Tensor K U (∀ s, X s) (∀ r, Y r))
    (P : Tensor K V (∀ s, X s) (∀ r, Y r)) (A : U → V → K)
    (hA : ∀ u x y, ∑ v, A u v * P v x y = T u x y) : SiteRestriction T P := by
  classical
  refine ⟨A, fun _ x' x => if x = x' then 1 else 0,
    fun _ y' y => if y = y' then 1 else 0, ?_⟩
  funext u x y
  simp only [Tensor.restrict]
  simp_rw [Fintype.prod_boole, ← funext_iff]
  simpa [mul_ite, ite_mul] using (hA u x y).symm

/-- The private slice product restricts to the original tensor by maps at the
individual sites of `S` and `R` and one arbitrary matrix at their common site. -/
theorem siteRestriction_private_slice_product
    (T : Tensor K U (∀ s, X s) (∀ r, Y r))
    (left : Module.Basis I K (leftSliceSpace T))
    (right : Module.Basis J K (rightSliceSpace T)) :
    SiteRestriction T
      (fun (p : I × J) x y => (left p.1).val x * (right p.2).val y) := by
  obtain ⟨A, hA⟩ := sliceProduct_coefficients T left right
  apply siteRestriction_central_map _ _ A
  simpa only [Fintype.sum_prod_type] using hA

/-- Every tensor is a local restriction of the product of two copies: one
with all `R` indices at the common site, the other with all `S` indices there.
This uses the literal coordinate slices as the two private tensors. -/
theorem siteRestriction_grouped_product [Fintype U]
    (T : Tensor K U (∀ s, X s) (∀ r, Y r)) :
    SiteRestriction T
      (fun (p : (U × (∀ r, Y r)) × (U × (∀ s, X s))) x y =>
        T p.1.1 x p.1.2 * T p.2.1 p.2.2 y) := by
  classical
  let L : (U × (∀ r, Y r)) → (∀ s, X s) → K := fun p x => T p.1 x p.2
  let Rw : (U × (∀ s, X s)) → (∀ r, Y r) → K := fun p => T p.1 p.2
  let left := Module.finBasis K (leftSliceSpace T)
  let right := Module.finBasis K (rightSliceSpace T)
  obtain ⟨core, hcore⟩ := sliceProduct_coefficients T left right
  obtain ⟨P, hP⟩ := (groupedSliceBasis_mutualRestriction L left).2
  obtain ⟨Q, hQ⟩ := (groupedSliceBasis_mutualRestriction Rw right).2
  let A (u : U) (p : (U × (∀ r, Y r)) × (U × (∀ s, X s))) :=
    ∑ ij, core u ij * (P ij.1 p.1 * Q ij.2 p.2)
  apply siteRestriction_central_map _ _ A
  intro u x y
  change ∑ p, A u p * (L p.1 x * Rw p.2 y) = T u x y
  calc
    _ = ∑ ij, ∑ p : (U × (∀ r, Y r)) × (U × (∀ s, X s)),
        (core u ij * (P ij.1 p.1 * Q ij.2 p.2)) * (L p.1 x * Rw p.2 y) := by
      simp only [A, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = ∑ ij, core u ij * ((∑ s, P ij.1 s * L s x) * ∑ r, Q ij.2 r * Rw r y) := by
      apply Finset.sum_congr rfl
      intro ij _
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = T u x y := by
      simp_rw [hP, hQ]
      rw [Fintype.sum_prod_type]
      apply hcore

end SpectralBooks
end LinearAlgebra
end OAI

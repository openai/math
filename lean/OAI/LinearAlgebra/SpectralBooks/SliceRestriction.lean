import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Restriction from the two private slice tensors

Let `U`, `B`, and `C` index coordinates of the common site and the two groups
of private sites. A basis vector of either slice space can have arbitrary
coefficients across all sites of that group. The restriction below acts only
on the common site, so it respects each private site individually.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation

variable {K U B C I J : Type*} [Field K]

/-- The span of the coordinate slices, hence of all contractions on the other sites. -/
def sliceSpace {A D : Type*} (rows : A → D → K) : Submodule K (D → K) :=
  Submodule.span K (Set.range rows)

/-- The private slice space on the group `B`. -/
def leftSliceSpace (T : Tensor K U B C) : Submodule K (B → K) :=
  sliceSpace (fun p : U × C => fun b => T p.1 b p.2)

/-- The private slice space on the group `C`. -/
def rightSliceSpace (T : Tensor K U B C) : Submodule K (C → K) :=
  sliceSpace (fun p : U × B => T p.1 p.2)

private def leftSlice (T : Tensor K U B C) (u : U) (c : C) : leftSliceSpace T :=
  ⟨fun b => T u b c, Submodule.subset_span ⟨(u, c), rfl⟩⟩

/-- Contracting the `B`-coordinates at fixed `u` yields a vector in the
`C` slice space. -/
private theorem dualSlice_mem [Fintype B] (T : Tensor K U B C) (u : U)
    (f : (B → K) →ₗ[K] K) :
    (fun c => f (fun b => T u b c)) ∈ rightSliceSpace T := by
  classical
  have h : (fun c => f (fun b => T u b c)) =
      ∑ b, f (Pi.single b 1) • T u b := by
    funext c
    conv_lhs => rw [pi_eq_sum_univ' (fun b => T u b c)]
    simp [mul_comm]
  rw [h]
  exact Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(u, b), rfl⟩)

private theorem basisExpansion {D : Type*} {W : Submodule K (D → K)}
    [Fintype I] (basis : Module.Basis I K W) (v : W) (d : D) :
    ∑ i, basis.repr v i * (basis i).val d = v.val d := by
  have h := congrArg (fun w : W => w.val d) (basis.sum_repr v)
  simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] using h

/-- Coordinate form of the local map from the product of the slice tensors.
The two basis indices are both input labels at the common site. -/
theorem sliceProduct_coefficients [Fintype B] [Fintype I] [Fintype J]
    (T : Tensor K U B C)
    (left : Module.Basis I K (leftSliceSpace T))
    (right : Module.Basis J K (rightSliceSpace T)) :
    ∃ A : U → I × J → K, ∀ u b c,
      ∑ i, ∑ j, A u (i, j) * ((left i).val b * (right j).val c) = T u b c := by
  classical
  choose f hf using fun i => (left.coord i).exists_extend
  let v (u : U) (i : I) : rightSliceSpace T :=
    ⟨fun c => f i (fun b => T u b c), dualSlice_mem T u (f i)⟩
  refine ⟨fun u p => right.repr (v u p.1) p.2, ?_⟩
  intro u b c
  calc
    _ = ∑ i, (∑ j, right.repr (v u i) j * (right j).val c) * (left i).val b := by
      simp only [Finset.sum_mul]
      congr 1
      funext i
      congr 1
      funext j
      ring
    _ = ∑ i, left.repr (leftSlice T u c) i * (left i).val b := by
      apply Finset.sum_congr rfl
      intro i _
      rw [basisExpansion]
      have he := DFunLike.congr_fun (hf i) (leftSlice T u c)
      exact congrArg (· * (left i).val b) he
    _ = T u b c := basisExpansion left (leftSlice T u c) b

/-- Multiplying the private tensors and applying a matrix at the common site
restricts their product to `T`. The maps on `B` and `C` are the canonical
identifications with the products with one-dimensional auxiliary legs. -/
theorem restrict_private_slice_product [Fintype B] [Fintype C] [Fintype I] [Fintype J]
    [DecidableEq B] [DecidableEq C]
    (T : Tensor K U B C)
    (left : Module.Basis I K (leftSliceSpace T))
    (right : Module.Basis J K (rightSliceSpace T)) :
    ∃ A : U → I × J → K,
      Tensor.restrict A
        (fun b (x : B × Unit) => if x.1 = b then (1 : K) else 0)
        (fun c (y : Unit × C) => if y.2 = c then (1 : K) else 0)
        (Tensor.product (fun i b (_ : Unit) => (left i).val b)
          (fun j (_ : Unit) c => (right j).val c)) = T := by
  obtain ⟨A, hA⟩ := sliceProduct_coefficients T left right
  refine ⟨A, ?_⟩
  funext u b c
  simpa [Tensor.restrict, Tensor.product, Fintype.sum_prod_type, mul_ite, ite_mul]
    using hA u b c

end SpectralBooks
end LinearAlgebra
end OAI

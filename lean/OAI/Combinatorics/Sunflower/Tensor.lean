import OAI.LinearAlgebra.SpectralBooks.MaskDiagonal

/-!
# Coefficient calculus for simultaneous local maps

A local matrix is indexed by its output basis followed by its input basis.
The coefficient formulas retain the matrices, which allows each site to choose
its matrix as a function of a control.
-/

open scoped BigOperators Classical
open OAI.LinearAlgebra.SpectralBooks
open OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower

noncomputable section

variable {S K : Type*} [Fintype S]
variable {A B C D : S → Type*}

/-- Apply one local matrix at each site to a coefficient tensor. -/
def contract [CommSemiring K] [∀ i, Fintype (A i)]
    (M : ∀ i, B i → A i → K) (T : (∀ i, A i) → K) (x : ∀ i, B i) : K :=
  ∑ a, T a * ∏ i, M i (x i) (a i)

theorem restrict_iff_contract [CommSemiring K] [∀ i, Fintype (A i)]
    (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) :
    Crossing.IsRestriction U T ↔ ∃ M : ∀ i, B i → A i → K, U = contract M T :=
  exists_congr fun _ => funext_iff.symm

/-- Expand a tensor given as a sum of coordinate basis tensors before applying local matrices. -/
theorem contract_basisTensor [CommSemiring K] [∀ i, Fintype (A i)]
    {L : Type*} [Fintype L] (M : ∀ i, B i → A i → K) (f : L → ∀ i, A i) (x : ∀ i, B i) :
    contract M (Crossing.basisTensor f) x =
      ∑ l, ∏ i, M i (x i) (f l i) := by
  unfold contract Crossing.basisTensor
  simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

/-- A common label is summed once, also when only a subset of the sites holds it. -/
theorem contract_maskDiagonal [Field K] (P : Finset S) (L : Type) [Fintype L]
    (M : ∀ i, B i → (Raw.maskDiagonal K P L).Leg i → K) (x : ∀ i, B i) :
    contract M (Raw.maskDiagonal K P L).coeff x =
      ∑ l : L, ∏ i, M i (x i) (fun _ => l) :=
  contract_basisTensor M (fun (l : L) _ _ => l) x

/-- The contraction of a basis label is a product of sitewise matrix entries. -/
theorem contract_basis [CommSemiring K] [∀ i, Fintype (A i)]
    (M : ∀ i, B i → A i → K) (a : ∀ i, A i) (x : ∀ i, B i) :
    contract M (fun y => if y = a then 1 else 0) x = ∏ i, M i (x i) (a i) := by
  simp [contract, ite_mul]

/-- Successive restrictions multiply the local matrices. -/
theorem contract_comp [CommSemiring K] [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (N : ∀ i, C i → B i → K) (M : ∀ i, B i → A i → K) (T : (∀ i, A i) → K) :
    contract N (contract M T) = contract (fun i c a => ∑ b, M i b a * N i c b) T := by
  funext x
  unfold contract
  simp_rw [Finset.sum_mul, Fintype.prod_sum, Finset.mul_sum, Finset.prod_mul_distrib,
    mul_assoc]
  exact Finset.sum_comm

/-- Independent resources transform under the Kronecker products of their local matrices. -/
theorem contract_mul [CommSemiring K] [∀ i, Fintype (A i)] [∀ i, Fintype (C i)]
    (M : ∀ i, B i → A i → K) (N : ∀ i, D i → C i → K)
    (T : (∀ i, A i) → K) (U : (∀ i, C i) → K) (x : ∀ i, B i × D i) :
    contract (fun i (v : B i × D i) (a : A i × C i) => M i v.1 a.1 * N i v.2 a.2)
        (fun a => T (fun i => (a i).1) * U (fun i => (a i).2)) x =
      contract M T (fun i => (x i).1) * contract N U (fun i => (x i).2) := by
  unfold contract
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow S A C) _ _ fun a => ?_
  simp only [Finset.prod_mul_distrib]
  ac_rfl

/-- Map each diagonal block into the same target and add its image. -/
theorem contract_addBlocks [CommSemiring K] [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (M : ∀ i, C i → A i → K) (N : ∀ i, C i → B i → K)
    (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) :
    contract (fun i c => Sum.elim (M i c) (N i c)) (sumCoeff T U) =
      contract M T + contract N U := by
  funext x
  simp only [contract, sumCoeff, add_mul, Finset.sum_add_distrib, sum_pushCoeff_mul,
    Pi.add_apply, Sum.elim_inl, Sum.elim_inr]

/-- Multiplying a single site's matrix by a scalar scales the output. -/
theorem contract_scaleAt [CommSemiring K] [∀ i, Fintype (A i)]
    (j : S) (z : K) (M : ∀ i, B i → A i → K) (T : (∀ i, A i) → K) (x : ∀ i, B i) :
    contract (fun i b a => (if i = j then z else 1) * M i b a) T x = z * contract M T x := by
  simp only [contract, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ,
    ite_true, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ac_rfl

/-- Subtract the second block by changing the sign at one site. -/
theorem contract_subBlocks [CommRing K] [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (j : S) (M : ∀ i, C i → A i → K) (N : ∀ i, C i → B i → K)
    (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) (x : ∀ i, C i) :
    contract (fun i c => Sum.elim (M i c) (fun b => (if i = j then -1 else 1) * N i c b))
        (sumCoeff T U) x =
      contract M T x - contract N U x := by
  rw [contract_addBlocks, Pi.add_apply, contract_scaleAt]
  ring

end

end Sunflower
end Combinatorics
end OAI

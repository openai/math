import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Upper.Tensor.Base

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

noncomputable section

/-!
# Heterogeneous direct sums and restrictions

The two summands retain separate coordinates on every leg. Cross coefficients
are zero, and block diagonal local matrices give actual restriction witnesses.
-/

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper.CoefficientTensor

section Algebra

variable {K X Y Z U V W X' Y' Z' U' V' W' : Type*} [CommSemiring K]

/-- Direct sum of tensors whose three coordinate spaces may all differ. -/
def blockSum (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X ⊕ U) (Y ⊕ V) (Z ⊕ W)
  | .inl x, .inl y, .inl z => T x y z
  | .inr u, .inr v, .inr w => S u v w
  | _, _, _ => 0

/-- Block diagonal local coefficient matrix, with no cross-summand maps. -/
def blockMatrix (A : X' → X → K) (D : U' → U → K) :
    (X' ⊕ U') → (X ⊕ U) → K
  | .inl x', .inl x => A x' x
  | .inr u', .inr u => D u' u
  | _, _ => 0

@[simp] theorem blockSum_inl (T : Tensor K X Y Z) (S : Tensor K U V W)
    (x : X) (y : Y) (z : Z) :
    blockSum T S (.inl x) (.inl y) (.inl z) = T x y z := rfl

@[simp] theorem blockSum_inr (T : Tensor K X Y Z) (S : Tensor K U V W)
    (u : U) (v : V) (w : W) :
    blockSum T S (.inr u) (.inr v) (.inr w) = S u v w := rfl

/-- Independent restrictions on the two summands combine into one restriction
on their full direct sum, including every vanishing cross coefficient. -/
theorem restrict_blockSum
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (D : U' → U → K) (E : V' → V → K) (F : W' → W → K)
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.restrict (blockMatrix A D) (blockMatrix B E) (blockMatrix C F)
      (blockSum T S) = blockSum (Tensor.restrict A B C T) (Tensor.restrict D E F S) := by
  funext x y z
  rcases x with x | u <;> rcases y with y | v <;> rcases z with z | w <;>
    simp [Tensor.restrict, blockSum, blockMatrix, Fintype.sum_sum_type]

/-- Relabel the coordinates of each summand independently. -/
theorem pullback_blockSum (T : Tensor K X Y Z) (S : Tensor K U V W)
    (a : X' → X) (b : Y' → Y) (c : Z' → Z)
    (d : U' → U) (e : V' → V) (f : W' → W) :
    Tensor.pullback (Sum.map a d) (Sum.map b e) (Sum.map c f) (blockSum T S) =
      blockSum (Tensor.pullback a b c T) (Tensor.pullback d e f S) := by
  funext x y z
  rcases x with x | u <;> rcases y with y | v <;> rcases z with z | w <;> rfl

end Algebra

section Restriction

variable {X Y Z U V W X' Y' Z' U' V' W' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]

/-- Restriction is compatible with heterogeneous tensor direct sums. -/
theorem Restricts.blockSum
    {T : Tensor Coeff X Y Z} {T' : Tensor Coeff X' Y' Z'}
    {S : Tensor Coeff U V W} {S' : Tensor Coeff U' V' W'}
    (hT : Restricts T T') (hS : Restricts S S') :
    Restricts (blockSum T S) (blockSum T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨blockMatrix A D, blockMatrix B E, blockMatrix C F,
    (restrict_blockSum A B C D E F T S).symm⟩

/-- Restriction is compatible with tensor products through the actual products
of the three local coefficient matrices. -/
theorem Restricts.product
    {T : Tensor Coeff X Y Z} {T' : Tensor Coeff X' Y' Z'}
    {S : Tensor Coeff U V W} {S' : Tensor Coeff U' V' W'}
    (hT : Restricts T T') (hS : Restricts S S') :
    Restricts (Tensor.product T S) (Tensor.product T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨fun x u => A x.1 u.1 * D x.2 u.2,
    fun y v => B y.1 v.1 * E y.2 v.2,
    fun z w => C z.1 w.1 * F z.2 w.2,
    (Tensor.restrict_product A B C D E F T S).symm⟩

end Restriction

end OAI.LinearAlgebra.MatrixExponent.Upper.CoefficientTensor

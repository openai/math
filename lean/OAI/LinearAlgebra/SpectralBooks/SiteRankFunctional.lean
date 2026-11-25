import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Diagonal
import OAI.LinearAlgebra.SpectralBooks.SpectralPoint
import OAI.LinearAlgebra.SpectralBooks.Spectrum
import Mathlib.Data.Fin.VecNotation

/-! # Evaluating three-site tensors at a finite-site spectral point

The site-indexed coefficient convention and the curried convention used by
matrix multiplication describe the same three-index arrays. In particular,
their products, diagonals, and three local restricting maps agree after
relabeling coordinates.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace SiteTensor

open MatrixMultiplication.Foundation
open scoped BigOperators Classical NNReal
noncomputable section

private def tuple {A : Fin 3 → Type*} (x : A 0) (y : A 1) (z : A 2) : ∀ i, A i :=
  Fin.cons x (Fin.cons y (Fin.cons z (fun i => i.elim0)))

private def coords (A : Fin 3 → Type*) : (∀ i, A i) ≃ A 0 × A 1 × A 2 :=
  (Fin.consEquiv A).symm.trans ((Equiv.refl _).prodCongr (piFinTwoEquiv _))

variable {F : Type*} [CommSemiring F] {X Y Z U V W : Type}
  [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]

/-- Regard a matrix-multiplication coefficient array as a tensor on three sites. -/
def ofThree (T : Tensor F X Y Z) : Raw (Fin 3) F where
  Leg := ![X, Y, Z]
  finiteLeg := tuple (inferInstanceAs (Fintype X)) (inferInstanceAs (Fintype Y)) (inferInstanceAs (Fintype Z))
  coeff := fun x => T (x 0) (x 1) (x 2)

/-- Local restriction agrees in the curried and site-indexed conventions. -/
theorem ofThree_restrict (T : Tensor F X Y Z) (A : U → X → F) (B : V → Y → F) (C : W → Z → F) :
    (ofThree (Tensor.restrict A B C T)).Restricts (ofThree T) := by
  let : DecidableEq (Fin 3) := fun i j => Classical.propDecidable (i = j)
  let M : ∀ i, (ofThree (Tensor.restrict A B C T)).Leg i → (ofThree T).Leg i → F := tuple A B C
  refine ⟨M, fun p => ?_⟩
  change (∑ x, ∑ y, ∑ z, A (p 0) x * B (p 1) y * C (p 2) z * T x y z) =
    ∑ q : (i : Fin 3) → (ofThree T).Leg i, T (q 0) (q 1) (q 2) * ∏ i, M i (p i) (q i)
  let e := coords (ofThree T).Leg
  calc
    _ = ∑ q : X × Y × Z, A (p 0) q.1 * B (p 1) q.2.1 * C (p 2) q.2.2 * T q.1 q.2.1 q.2.2 := by
      simp only [Fintype.sum_prod_type]
    _ = _ := by
      apply Fintype.sum_equiv e.symm
      intro q
      simp only [Fin.prod_univ_three]
      change A (p 0) q.1 * B (p 1) q.2.1 * C (p 2) q.2.2 * T q.1 q.2.1 q.2.2 =
        T q.1 q.2.1 q.2.2 * (A (p 0) q.1 * B (p 1) q.2.1 * C (p 2) q.2.2)
      ac_rfl

/-- The grouped tensor product in both coordinate conventions pairs the same three indices. -/
theorem ofThree_product (T : Tensor F X Y Z) (S : Tensor F U V W) :
    (ofThree (Tensor.product T S)).Equivalent ((ofThree T).mul (ofThree S)) := by
  let e : ∀ i, (ofThree (Tensor.product T S)).Leg i ≃ ((ofThree T).mul (ofThree S)).Leg i :=
    tuple (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
  apply Raw.reindex_equivalent e
  intro p
  rfl

private theorem diagonal_eq_sum {α : Type} [Fintype α] [DecidableEq α] (q : Fin 3 → α) :
    (if q 0 = q 1 ∧ q 0 = q 2 then (1 : F) else 0) =
      ∑ a : α, @ite F (q = fun _ => a) (Classical.propDecidable _) 1 0 := by
  have eq (a : α) : q = (fun _ => a) ↔ q 0 = a ∧ q 1 = a ∧ q 2 = a := by
    simp [funext_iff, Fin.forall_fin_succ]
  simp_rw [eq]
  rw [Finset.sum_eq_single (q 0)]
  · simp [eq_comm]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- The full diagonal in the rank model is the common-label site diagonal. -/
theorem ofThree_diagonal (α : Type) [Fintype α] [DecidableEq α] :
    (ofThree (Tensor.diagonal (K := F) α)).Equivalent (Raw.diagonal (Fin 3) F α) := by
  let e : ∀ i, (ofThree (Tensor.diagonal (K := F) α)).Leg i ≃ α :=
    tuple (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
  apply Raw.reindex_equivalent e
  intro x
  exact diagonal_eq_sum (F := F) (fun i => e i (x i))

/-- Evaluation at a normalized three-site spectral point gives the multiplicative,
restriction-monotone functional used for the rectangular rank bounds. -/
def rankFunctionalOfSpectrum {K : Type*} [Field K]
    (f : normalizedSpectrum (fun x y : TensorClass.{0} (Fin 3) K => x ≤ y)) : RankFunctional K where
  value T := f.1 (ofRaw (ofThree T))
  diagonal r := by
    rw [ofRaw_eq_iff.mpr (ofThree_diagonal (F := K) (Fin r)), ofRaw_diagonal_fin_eq_natCast]
    exact map_natCast (normalizedSpectrum.toRingHom f) r
  product T S := by
    rw [ofRaw_eq_iff.mpr (ofThree_product T S), ofRaw_mul]
    exact f.2.2.2.2.1 _ _
  restrict_le T A B C := f.2.2.2.2.2 _ _ (ofRaw_le_iff.mpr (ofThree_restrict T A B C))

end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI

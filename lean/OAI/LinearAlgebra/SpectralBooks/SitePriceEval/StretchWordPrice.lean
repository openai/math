import OAI.LinearAlgebra.SpectralBooks.StretchProducts

/-! # Additivity of price on product words -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Foundation
open scoped Classical BigOperators

namespace SitePriceEval
open PermutationControl

variable {K : Type*} [Field K] {B C : Type} [Fintype B] [Fintype C]
  (p : SitePriceEval K B C) (hmul : p.BinaryProductAdditive)

include hmul

private theorem value_finWordProduct {U L : Type} {X : B → Type} {Y : C → Type}
    [Fintype U] [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]
    (T : L → Tensor K U (∀ b, X b) (∀ c, Y c)) (hT : ∀ l, T l ≠ 0)
    (n : ℕ) (s : Fin n → L) :
    p.value (wordProduct T s) = ∑ j, p.value (T (s j)) := by
  induction n with
  | zero =>
    let W := wordProduct T s
    let e (V : Type) : (Fin 0 → V) ≃ (Fin 0 → V) × (Fin 0 → V) :=
      (Equiv.prodUnique _ _).symm
    have hW := wordProduct_ne_zero T hT s
    have hself : p.value W = p.value (splitProduct W W) := by
      apply p.value_reindex (e U) (fun b => e (X b)) (fun c => e (Y c))
      intros
      simp [splitProduct, W, wordProduct]
    rw [hmul W W hW hW] at hself
    simpa [W] using (show p.value W = 0 by linarith only [hself])
  | succ n ih =>
    let tail : Fin n → L := s ∘ Fin.succ
    let e (V : Type) := (Fin.consEquiv (fun _ : Fin (n + 1) => V)).symm
    have he : p.value (wordProduct T s) =
        p.value (splitProduct (T (s 0)) (wordProduct T tail)) := by
      apply p.value_reindex (e U) (fun b => e (X b)) (fun c => e (Y c))
      intro u x y
      exact Fin.prod_univ_succ (fun j => T (s j) (u j) (fun b => x b j) (fun c => y c j))
    rw [he, hmul _ _ (hT _) (wordProduct_ne_zero T hT _), ih, Fin.sum_univ_succ]
    rfl

/-- Binary product additivity implies the sum formula for any finite word, even
the empty word. Its coefficient tensor has one coordinate at every site and is
isomorphic to its square. -/
theorem wordProductAdditive_of_binaryProductAdditive : p.WordProductAdditive := by
  intro J L U X Y _ _ _ _ _ T hT s
  let e := Fintype.equivFin J
  let read (V : Type) := e.arrowCongr (Equiv.refl V)
  have he : p.value (wordProduct T s) = p.value (wordProduct T (s ∘ e.symm)) := by
    apply p.value_reindex (read U) (fun b => read (X b)) (fun c => read (Y c))
    intro u x y
    exact (Equiv.prod_comp e.symm (fun j => T (s j) (u j) (fun b => x b j) (fun c => y c j))).symm
  rw [he, value_finWordProduct p hmul T hT]
  exact Equiv.sum_comp e.symm (fun j => p.value (T (s j)))

end SitePriceEval

end SpectralBooks
end LinearAlgebra
end OAI

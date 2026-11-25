import OAI.Hierarchy.TaggedRadixStages
import OAI.Hierarchy.CorrectionFrame

namespace OAI
/-! # Parallel radix stages with one product socket

Each block has its own input and output rows. The oracle pins of all blocks
are laid out consecutively, so filling the one exposed socket with the data
product evaluates all blocks independently.
-/

noncomputable section
namespace Hierarchy.Tagged.RadixStage

open ThreeFlat Routing
open CorrectionFrame (dataProduct)
open scoped BigOperators Classical

variable {F : Type*} {I O : Type} [Fintype I] [Fintype O] {s q : ℕ}

private def parallelPin (i : Fin s) :
    Pins I O (Fin q) → Pins (Fin s × I) (Fin s × O) (Fin (s*q))
  | .inl (.inl j) => .inl (.inl (i,j))
  | .inl (.inr j) => .inl (.inr (i,j))
  | .inr j => .inr (finProdFinEquiv (i,j))

/-- Place the blocks in parallel and concatenate their oracle pins. -/
def parallel (N : Fin s → Network F I O (Fin q)) :
    Network F (Fin s × I) (Fin s × O) (Fin (s*q)) :=
  TypedWiring.glue (port := fun _ => Pins I O (Fin q)) (H := Fin 0) N
    (fun i j => .inl (parallelPin i j))

@[simp] theorem parallel_cells (N : Fin s → Network F I O (Fin q)) :
    (parallel N).cells = ∑ i, (N i).cells := by simp [parallel]

@[simp] theorem parallel_internal (N : Fin s → Network F I O (Fin q)) :
    (parallel N).internal = ∑ i, (N i).internal := by simp [parallel]

theorem parallel_row [CommSemiring F] (N : Fin s → Network F I O (Fin q))
    (x : Fin s × I → Bool) (y : Fin s × O → Bool) (z : Fin (s*q) → Bool) :
    row (parallel N) x y z = ∏ i, row (N i) (fun j => x (i,j)) (fun j => y (i,j))
      (fun j => z (finProdFinEquiv (i,j))) := by
  unfold row parallel
  rw [TypedWiring.glue_value, Fintype.sum_unique]
  apply Finset.prod_congr rfl
  intro i _
  apply congrArg (TypedWiring.value (N i))
  funext j
  rcases j with (j | j) | j <;> rfl

/-- Contraction at the one product socket is the product of the separate contractions. -/
theorem parallel_contract [CommSemiring F] (N : Fin s → Network F I O (Fin q))
    (φ : (Fin q → Bool) → F) (x : Fin s × I → Bool) (y : Fin s × O → Bool) :
    contract (parallel N) (dataProduct s φ) x y =
      ∏ i, contract (N i) φ (fun j => x (i,j)) (fun j => y (i,j)) := by
  unfold contract dataProduct
  simp_rw [parallel_row, ← Finset.prod_mul_distrib]
  let e : (Fin (s*q) → Bool) ≃ (Fin s → Fin q → Bool) :=
    (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)
  let g (i : Fin s) (b : Fin q → Bool) :=
    row (N i) (fun j => x (i,j)) (fun j => y (i,j)) b * φ b
  calc
    _ = ∑ z : Fin (s*q) → Bool, ∏ i, g i (fun j => z (finProdFinEquiv (i,j))) := by
      apply Finset.sum_congr (congrArg (@Finset.univ (Fin (s*q) → Bool)) (Subsingleton.elim _ _))
      intro z _
      rfl
    _ = ∑ b : Fin s → Fin q → Bool, ∏ i, g i (b i) := by
      apply Fintype.sum_equiv e
      intro z
      rfl
    _ = ∏ i, ∑ b : Fin q → Bool, g i b := by
      refine Eq.trans ?_ (Fintype.prod_sum g).symm
      apply Finset.sum_congr
        (congrArg (@Finset.univ (Fin s → Fin q → Bool)) (Subsingleton.elim _ _))
      intro z _
      rfl
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.sum_congr (congrArg (@Finset.univ (Fin q → Bool)) (Subsingleton.elim _ _))
      intro b _
      rfl

/-- The complete output array is forced block by block, including an empty bank. -/
theorem parallel_computesOn [CommSemiring F] (N : Fin s → Network F I O (Fin q))
    (φ : (Fin q → Bool) → F) (run : Fin s → (I → Bool) → O → Bool)
    (valid : Fin s → (I → Bool) → Prop)
    (ok : ∀ i, ComputesOn (N i) φ (valid i) (run i)) :
    ComputesOn (parallel N) (dataProduct s φ) (fun x => ∀ i, valid i (fun j => x (i,j)))
      (fun x p => run p.1 (fun j => x (p.1,j)) p.2) := by
  intro x hx y
  have same : (∀ i, (fun j => y (i,j)) = run i (fun j => x (i,j))) ↔
      y = fun p => run p.1 (fun j => x (p.1,j)) p.2 := by
    constructor
    · intro he
      funext ⟨i,j⟩
      exact congrFun (he i) j
    · rintro rfl i
      rfl
  rw [parallel_contract]
  simp only [fun i => ok i _ (hx i), Fintype.prod_boole, same]

theorem parallel_computes [CommSemiring F] (N : Fin s → Network F I O (Fin q))
    (φ : (Fin q → Bool) → F) (run : Fin s → (I → Bool) → O → Bool)
    (ok : ∀ i, Computes (N i) φ (run i)) :
    Computes (parallel N) (dataProduct s φ)
      (fun x p => run p.1 (fun j => x (p.1,j)) p.2) :=
  fun x => parallel_computesOn N φ run (fun _ _ => True)
    (fun i a _ => ok i a) x (fun _ => trivial)


end Hierarchy.Tagged.RadixStage

end
end OAI

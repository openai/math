import OAI.Computability.BorderVNP.ShortenPublicPopulationRows

/-! # Stable-name batch of the actual moved segment classifiers

Each occupied cable's motion and tag computation is run once. Rows can
share the pack's translation or any earlier public computations. The following
stage reads all tiles and tags simultaneously while retaining the original
charge and width wires.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicPopulation

open Cover Cover.AddressCircuit ParseBatchSort ParseBatchCounts
open VPVNP.VerifierNetwork (Frame)
open scoped BigOperators

variable {U σ : Type*} {B : Type} [Fintype U] [Fintype B] [Fintype σ] {q l r w D : ℕ}
    (row : U → Frame σ (ProductSlots q l ⊕ B))

private noncomputable def classifiers : Frame σ (U × (ProductSlots q l ⊕ B)) :=
  (Crossing.exists_parallelFrames (out := fun _ : U => ProductSlots q l ⊕ B) row).choose.select
    (fun uj => ⟨uj.1,uj.2⟩)

private theorem classifiers_size : (classifiers row).size ≤ 1 + ∑ u, (row u).size := by
  simpa only [classifiers,Frame.select_size] using
    (Crossing.exists_parallelFrames (out := fun _ : U => ProductSlots q l ⊕ B) row).choose_spec.1

private theorem classifiers_eval (x : σ → Bool) (u : U) (j : ProductSlots q l ⊕ B) :
    (classifiers row).eval x (u,j) = (row u).eval x j := by
  simpa only [classifiers, Frame.select_eval] using
    (Crossing.exists_parallelFrames (out := fun _ : U => ProductSlots q l ⊕ B) row).choose_spec.2 x u j

variable (code : B ↪ Fin (2^r)) (active : U → σ) (width : U → Fin w → σ)

/-- Run each row frame and form all true bin counts with a single shared sparse scan. -/
noncomputable def movedRows : Frame σ (((Fin q → Deck l) × B) × Fin w) :=
  (fromRows (fun u b => .inr (u,.inr b)) code (Sum.inl ∘ active) (fun u j => .inr (u,.inl j))
    (fun u => Sum.inl ∘ width u)).subst (classifiers row).withInput

/-- Each row program's gate charge is counted once. There is no product
of row count with the number of absolute tiles. -/
theorem movedRows_size :
    let n := Fintype.card U + Fintype.card (Fin q → Deck l)*Fintype.card B
    (movedRows row code active width).size ≤ 1 + (∑ u, (row u).size) +
      (Fintype.card U*r*(2*Fintype.card B+1) + 2*(n+1)*laneCost (Nat.clog 2 n) (r+keyWidth q l) w) := by
  intro n
  rw [movedRows,Frame.subst_size,Frame.withInput_size]
  exact Nat.add_le_add (classifiers_size row) (fromRows_size _ _ _ _ _)

variable {P : Type*} {bits : P → ℕ} (N : Crossing.Network D P bits)
    (bin : N.Edge → Option ((Fin q → Deck l) × B)) (slot : N.Edge ↪ U)

/-- The wired batch returns the exact population of the network's moved
bin, using the one-row classifier equality only at live cable names. -/
theorem movedRows_count (x : σ → Bool)
    (enabled : ∀ e, x (active (slot e)) = (bin e).isSome)
    (empty : ∀ u, u ∉ Set.range slot → x (active u) = false)
    (tileWord : ∀ e a, bin e = some a → ∀ j, (row (slot e)).eval x (.inl j) = productWires l a.1 j)
    (tag : ∀ e a, bin e = some a → ∀ c, (row (slot e)).eval x (.inr c) = true ↔ c = a.2)
    (widthWord : ∀ e a, bin e = some a → value (x ∘ width (slot e)) = N.width e)
    (fits : ∀ a, SeedIntervals.count N bin a < 2^w) (a : (Fin q → Deck l) × B) :
    value (fun j => (movedRows row code active width).eval x (a,j)) = SeedIntervals.count N bin a := by
  simp only [movedRows, Frame.subst_eval]
  refine fromRows_count (fun u b => Sum.inr (u,Sum.inr b)) code (Sum.inl ∘ active)
    (fun u j => Sum.inr (u,Sum.inl j)) (fun u => Sum.inl ∘ width u) N bin slot
    ((classifiers row).withInput.eval x) ?_ ?_ ?_ ?_ ?_ fits a
  · simpa only [Function.comp_apply,Frame.withInput_eval_inl] using enabled
  · simpa only [Function.comp_apply,Frame.withInput_eval_inl] using empty
  · intro e b hb
    funext j
    rw [Function.comp_apply,Frame.withInput_eval_inr,classifiers_eval,tileWord e b hb]
  · intro e b hb c
    rw [Frame.withInput_eval_inr,classifiers_eval,tag e b hb]
  · simpa only [Function.comp_def,Frame.withInput_eval_inl] using widthWord

end Shortening.PublicPopulation

end BorderVNP
end Computability
end OAI

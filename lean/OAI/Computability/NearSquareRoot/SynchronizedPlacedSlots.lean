import OAI.Computability.NearSquareRoot.SynchronizedBlockSlots
import OAI.Computability.NearSquareRoot.SynchronizedPlacedWord

/-! # Placed permutation and phase slots

Each occupied cell uses the permutation or phase of its local coordinate. Every
cell outside the placement stays fixed, with phase one.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix

variable {X J A : Type} [Fintype X] [Fintype J] [DecidableEq A]

/-- Apply the same permutation in each placed fiber. -/
def placedSlotPermutation (e : X × J ↪ A) (p : Equiv.Perm X) : Equiv.Perm A :=
  Equiv.Perm.viaFintypeEmbedding (p.prodCongr (Equiv.refl J)) e

@[simp] theorem placedSlotPermutation_apply (e : X × J ↪ A) (p : Equiv.Perm X) (x : X) (j : J) :
    placedSlotPermutation e p (e (x, j)) = e (p x, j) := by
  exact Equiv.Perm.viaFintypeEmbedding_apply_image (p.prodCongr (Equiv.refl J)) e (x, j)

theorem placedSlotPermutation_outside (e : X × J ↪ A) (p : Equiv.Perm X) {u : A}
    (hu : u ∉ Set.range e) : placedSlotPermutation e p u = u :=
  Equiv.Perm.viaFintypeEmbedding_apply_notMem_range (p.prodCongr (Equiv.refl J)) e hu

/-- Read the local phase at the unique preimage, with unit phase on spare cells. -/
def placedSlotPhase (e : X × J ↪ A) (d : X → ℂ) (u : A) : ℂ :=
  if h : u ∈ Set.range e then d (e.toEquivRange.symm ⟨u, h⟩).1 else 1

@[simp] theorem placedSlotPhase_apply (e : X × J ↪ A) (d : X → ℂ) (x : X) (j : J) :
    placedSlotPhase e d (e (x, j)) = d x := by
  simp [placedSlotPhase]

theorem placedSlotPhase_outside (e : X × J ↪ A) (d : X → ℂ) {u : A} (hu : u ∉ Set.range e) :
    placedSlotPhase e d u = 1 := by simp [placedSlotPhase, hu]

theorem placedSlotPhase_norm (e : X × J ↪ A) (d : X → ℂ) (hd : ∀ x, ‖d x‖ = 1) (u : A) :
    ‖placedSlotPhase e d u‖ = 1 := by
  by_cases hu : u ∈ Set.range e
  · obtain ⟨⟨x, j⟩, rfl⟩ := hu
    simp [hd]
  · simp [placedSlotPhase_outside _ _ hu]

/-- Compute the physical permutation from any correct inverse address lookup. -/
theorem placedSlotPermutation_lookup (e : X × J ↪ A) (p : Equiv.Perm X)
    (lookup : A → Option (X × J)) (hl : ∀ u v, lookup u = some v ↔ e v = u) (u : A) :
    placedSlotPermutation e p u = ((lookup u).map fun v => e (p v.1, v.2)).getD u := by
  cases h : lookup u with
  | none =>
    apply placedSlotPermutation_outside
    rintro ⟨v, hv⟩
    simpa [h] using (hl u v).2 hv
  | some v =>
    obtain ⟨x, j⟩ := v
    rw [← (hl u _).1 h]
    exact placedSlotPermutation_apply e p x j

/-- Compute the phase table from the same inverse address lookup. -/
theorem placedSlotPhase_lookup (e : X × J ↪ A) (d : X → ℂ)
    (lookup : A → Option (X × J)) (hl : ∀ u v, lookup u = some v ↔ e v = u) (u : A) :
    placedSlotPhase e d u = ((lookup u).map fun v => d v.1).getD 1 := by
  cases h : lookup u with
  | none =>
    apply placedSlotPhase_outside
    rintro ⟨v, hv⟩
    simpa [h] using (hl u v).2 hv
  | some v =>
    obtain ⟨x, j⟩ := v
    rw [← (hl u _).1 h]
    exact placedSlotPhase_apply e d x j

variable [Fintype A] [DecidableEq X] [DecidableEq J] {S : Type} [DecidableEq S]

/-- The physical permutation slot acts as the placed permutation matrix. -/
theorem placedSlotPermutation_matrix (e : X × J ↪ A) (bits : A ≃ Fin 2 × S) (p : Equiv.Perm X) :
    Slot.matrix bits (.permutation (placedSlotPermutation e p)) = placeHom e p.toPEquiv.toMatrix := by
  apply Matrix.ext_iff_mulVec.mpr
  intro z
  funext u
  change ((placedSlotPermutation e p).toPEquiv.toMatrix *ᵥ z) u = _
  rw [PEquiv.toMatrix_toPEquiv_mulVec, placeHom_mulVec]
  change z (placedSlotPermutation e p u) = _
  by_cases hu : u ∈ Set.range e
  · obtain ⟨⟨x, j⟩, rfl⟩ := hu
    rw [e.injective.extend_apply, placedSlotPermutation_apply, PEquiv.toMatrix_toPEquiv_mulVec]
    rfl
  · rw [Function.extend_apply' _ _ _ hu, placedSlotPermutation_outside _ _ hu]

/-- The physical phase slot acts as the placed diagonal matrix. -/
theorem placedSlotPhase_matrix (e : X × J ↪ A) (bits : A ≃ Fin 2 × S) (d : X → ℂ)
    (hd : ∀ x, ‖d x‖ = 1) :
    Slot.matrix bits (.phase (placedSlotPhase e d) (placedSlotPhase_norm e d hd)) =
      placeHom e (diagonal d) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro z
  funext u
  change (diagonal (placedSlotPhase e d) *ᵥ z) u = _
  rw [mulVec_diagonal, placeHom_mulVec]
  by_cases hu : u ∈ Set.range e
  · obtain ⟨⟨x, j⟩, rfl⟩ := hu
    rw [e.injective.extend_apply, placedSlotPhase_apply, mulVec_diagonal]
  · rw [Function.extend_apply' _ _ _ hu, placedSlotPhase_outside _ _ hu, one_mul]

end ShortFourier

end NearSquareRoot
end Computability
end OAI

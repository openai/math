import OAI.Computability.BorderVNP.PackedCellAddressOutputs

/-! # Supplied input buffer addresses of crossing and argument bits

The local macro prepends its guessed words to the supplied input buffer.
Subtracting the private end from a compiled absolute address gives the live
slot in the external buffer, including at width-one and zero-width boundaries.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CellAddresses

open Crossing
open scoped Classical

variable {D m n : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {C : Type} (cell : N.Site → C) (c : C) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)

/-- Every bit of the supplied buffer belongs to exactly one crossing incidence or argument port. -/
theorem supplied_unique (i : Fin (suppliedSize N cell c)) :
    ∃! q : Σ u : Supplied N cell c, Fin (suppliedWidth N cell c u),
      suppliedOrdinal N cell c edgeID portID q.1 q.2 = i := by
  let f := CellSlabs.ordinal (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c)
  exact ⟨f.symm i, f.apply_symm_apply i, fun q h => f.injective (h.trans (f.apply_symm_apply i).symm)⟩

end Packing.CellAddresses

namespace Packing.CellAddressViews

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical ParseBatchSort
open scoped Classical

variable {D s m n C d k w : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → Fin C) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
variable (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)
variable {x : σ → Bool} (h : Represents N cell aux siteID edgeID portID F x)
variable (fit : ∀ c, guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c < 2^w)

/-- Compiled external input address after stripping the private prefix of its cell. -/
noncomputable def suppliedSlot (x : σ → Bool) (c : Fin C) (view : View s m n C) (lane : ℕ) : ℕ :=
  value (fun j => (frame F).eval x (view,j)) + lane -
    value (fun j => (frame F).eval x (.inr (.inr (1,c)),j))

include h fit

/-- Scattering a crossing word to its source cell fills exactly that incidence's external bits. -/
theorem source_slot (e : N.CrossingEdge cell) (i : Fin (N.width e.val)) :
    let c := cell (N.src e.val)
    suppliedSlot F x c (.inl (.inl (.inl (edgeID e.val)))) i.val =
      (suppliedOrdinal N cell c edgeID portID (.inl ⟨e,.inl rfl⟩) i).val := by
  intro c
  rw [suppliedSlot,source_value N cell aux siteID edgeID portID F h fit,
    marker_value N cell aux siteID edgeID portID F h fit]
  simp only [wireBase,e.property,dite_false,externalBase,show (1 : Fin 3) ≠ 0 by decide,
    show (1 : Fin 3) ≠ 2 by decide,ite_false,add_zero,c]
  rw [Nat.add_assoc,Nat.add_sub_cancel_left]
  rfl

/-- The destination has its own supplied slot, even when a source and a destination number coincide across cells. -/
theorem dest_slot (e : N.CrossingEdge cell) (i : Fin (N.width e.val)) :
    let c := cell (N.dst e.val)
    suppliedSlot F x c (.inl (.inl (.inr (edgeID e.val)))) i.val =
      (suppliedOrdinal N cell c edgeID portID (.inl ⟨e,.inr rfl⟩) i).val := by
  intro c
  rw [suppliedSlot,dest_value N cell aux siteID edgeID portID F h fit,
    marker_value N cell aux siteID edgeID portID F h fit]
  simp only [wireBase,e.property,dite_false,externalBase,show (1 : Fin 3) ≠ 0 by decide,
    show (1 : Fin 3) ≠ 2 by decide,ite_false,add_zero,c]
  rw [Nat.add_assoc,Nat.add_sub_cancel_left]
  rfl

/-- Every bit delivered to an external port lands at its exact typed position in the supplied buffer. -/
theorem port_slot (p : P) (i : Fin (bits p)) :
    let c := cell (N.attach p)
    suppliedSlot F x c (.inl (.inr (portID p))) i.val =
      (suppliedOrdinal N cell c edgeID portID (.inr ⟨p,rfl⟩) i).val := by
  intro c
  rw [suppliedSlot,port_value N cell aux siteID edgeID portID F h fit,
    marker_value N cell aux siteID edgeID portID F h fit]
  simp only [portBase,externalBase,show (1 : Fin 3) ≠ 0 by decide,
    show (1 : Fin 3) ≠ 2 by decide,ite_false,add_zero,c]
  rw [Nat.add_assoc,Nat.add_sub_cancel_left]
  rfl

end Packing.CellAddressViews

end BorderVNP
end Computability
end OAI

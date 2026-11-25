import OAI.Computability.BorderVNP.PackedSuppliedOffsets

/-! # The supplied offsets at true crossing ends and grouped ports -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SuppliedOffsets

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical CellAddressViews ParseBatchSort
open private srcKey dstKey portKey from OAI.Computability.BorderVNP.PackedCellAddressPhysical
open scoped Classical

variable {D s m n C d k w : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → Fin C) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
variable (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)
variable {x : σ → Bool} (h : Represents N cell aux siteID edgeID portID F x)
variable (fit : ∀ c, guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c < 2^w)

include h fit

/-- Source-relative address plus lane is the true supplied wire index in the source's cell. -/
theorem source_lane (e : N.CrossingEdge cell) (i : Fin (N.width e.val)) :
    let c := cell (N.src e.val)
    value (fun j => (frame F).eval x (.inl (.inl (.inl (edgeID e.val))),j))+i.val =
      (suppliedOrdinal N cell c edgeID portID (.inl ⟨e,.inl rfl⟩) i).val := by
  intro c
  rw [endpoint_value F x _ c (srcKey N cell aux siteID edgeID portID F h _)]
  let zero : Fin (N.width e.val) := ⟨0,Nat.zero_lt_of_lt i.isLt⟩
  have eq := source_slot N cell aux siteID edgeID portID F h fit e zero
  change suppliedSlot F x c _ 0 = _ at eq
  rw [eq]
  rfl

/-- Destination-relative address plus lane is the true supplied wire index in its own cell. -/
theorem dest_lane (e : N.CrossingEdge cell) (i : Fin (N.width e.val)) :
    let c := cell (N.dst e.val)
    value (fun j => (frame F).eval x (.inl (.inl (.inr (edgeID e.val))),j))+i.val =
      (suppliedOrdinal N cell c edgeID portID (.inl ⟨e,.inr rfl⟩) i).val := by
  intro c
  rw [endpoint_value F x _ c (dstKey N cell aux siteID edgeID portID F h _)]
  let zero : Fin (N.width e.val) := ⟨0,Nat.zero_lt_of_lt i.isLt⟩
  have eq := dest_slot N cell aux siteID edgeID portID F h fit e zero
  change suppliedSlot F x c _ 0 = _ at eq
  rw [eq]
  rfl

/-- The slot at an external port is its typed bank prefix even when its width is zero. -/
theorem port_base (p : P) :
    let c := cell (N.attach p)
    value (fun j => (frame F).eval x (.inl (.inr (portID p)),j)) =
      CellSlabs.start (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c) (.inr ⟨p,rfl⟩) := by
  intro c
  rw [endpoint_value F x _ c (portKey N cell aux siteID edgeID portID F h _),suppliedSlot,
    port_value N cell aux siteID edgeID portID F h fit,marker_value N cell aux siteID edgeID portID F h fit]
  simp [portBase,externalBase,c]
  unfold CellSlabs.start
  congr 2; exact Subsingleton.elim _ _

/-- The output consumed by the private-description prefix pass is the real complete
size of the supplied bank in the chosen cell. -/
theorem cell_size (c : Fin C) :
    value (fun j => (frame F).eval x (.inr c,j)) = suppliedSize N cell c := by
  rw [size_value F x c,marker_value N cell aux siteID edgeID portID F h fit,
    marker_value N cell aux siteID edgeID portID F h fit]
  simp

end Packing.SuppliedOffsets

end BorderVNP
end Computability
end OAI

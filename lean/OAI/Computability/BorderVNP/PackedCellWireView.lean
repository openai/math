import OAI.Computability.BorderVNP.PackedCellAddressRead

/-! # Viewing one cell's physical wire inputs as a network assignment

Every incident edge has one unambiguous word, supplied at a crossing or
guessed at an internal wire. Extending these words by zero away from the
cell provides a full network assignment with exactly the local checker reads.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CellAddresses

open Crossing
open scoped Classical

variable {D m n : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
  {C : Type} (cell : N.Site → C) (c : C) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)

/-- Complete the physical cable words at this cell to an assignment on the full layout. -/
noncomputable def assignment (g : Fin (guessedSize N cell c) → Bool)
    (x : Fin (suppliedSize N cell c) → Bool) : N.Assignment := fun e k =>
  if hi : cell (N.src e) = c ∧ cell (N.dst e) = c then
    guessedWords N cell c edgeID g ⟨e,hi⟩ k
  else if ho : cell (N.src e) = c ∨ cell (N.dst e) = c then
    let cross : cell (N.src e) ≠ cell (N.dst e) := fun h => hi (by rcases ho with h'|h' <;> simp_all)
    suppliedWords N cell c edgeID portID x (.inl ⟨⟨e,cross⟩,ho⟩) k
  else false

/-- Every original site in the cell sees the completed assignment at every incident bit. -/
theorem assignment_wire (g : Fin (guessedSize N cell c) → Bool) (x : Fin (suppliedSize N cell c) → Bool)
    (v : {v : N.Site // cell v = c}) (e : {e : N.Edge // N.src e = v.val ∨ N.dst e = v.val})
    (k : Fin (N.width e.val)) :
    (wire N cell c edgeID portID v e k).elim g x = assignment N cell c edgeID portID g x e.val k := by
  have hv : cell (N.src e.val) = c ∨ cell (N.dst e.val) = c := e.property.imp
    (fun h => (congrArg cell h).trans v.property) (fun h => (congrArg cell h).trans v.property)
  by_cases hs : cell (N.src e.val) = cell (N.dst e.val)
  · have hi : cell (N.src e.val) = c ∧ cell (N.dst e.val) = c := by rcases hv with h|h <;> simp_all
    simp only [assignment,dite_eq_left hi,wire,dite_eq_left hs]
    rfl
  · have hi : ¬ (cell (N.src e.val) = c ∧ cell (N.dst e.val) = c) := fun h => hs (h.1.trans h.2.symm)
    simp only [assignment,dite_eq_right hi,dite_eq_left hv,wire,dite_eq_right hs,Sum.elim_inr]
    rfl

/-- A local bank lookup at the canonical cable base reads this full assignment. -/
theorem assignment_at (aux : N.Site → ℕ) (g : Fin (guessedSize N cell c) → Bool)
    (a : Fin (siteSize N cell c aux) → Bool) (x : Fin (suppliedSize N cell c) → Bool)
    (v : {v : N.Site // cell v = c}) (e : {e : N.Edge // N.src e = v.val ∨ N.dst e = v.val})
    (k : Fin (N.width e.val)) :
    CellSparse.lookup (bank N cell c aux g a x) (wireBase N cell c edgeID portID aux v e + k.val) =
      assignment N cell c edgeID portID g x e.val k :=
  (wire_at N cell c edgeID portID aux g a x v e k).trans (assignment_wire N cell c edgeID portID g x v e k)

/-- Complete the actual external port inputs of a cell by zero at other cells. -/
noncomputable def external (x : Fin (suppliedSize N cell c) → Bool) : Ports bits := fun p k =>
  if h : cell (N.attach p) = c then suppliedWords N cell c edgeID portID x (.inr ⟨p,h⟩) k else false

/-- The exterior word read at an attached argument port agrees with its physical
address in the supplied bit block. -/
theorem external_port (x : Fin (suppliedSize N cell c) → Bool) (v : {v : N.Site // cell v = c})
    (p : {p : P // N.attach p = v.val}) (k : Fin (bits p.val)) :
    x (port N cell c edgeID portID v p k) = external N cell c edgeID portID x p.val k := by
  have h := (congrArg cell p.property).trans v.property
  rw [external,dite_eq_left h]
  rfl

/-- Lookup at the external base yields the completed external-port assignment. -/
theorem external_at (aux : N.Site → ℕ) (g : Fin (guessedSize N cell c) → Bool)
    (a : Fin (siteSize N cell c aux) → Bool) (x : Fin (suppliedSize N cell c) → Bool)
    (v : {v : N.Site // cell v = c}) (p : {p : P // N.attach p = v.val}) (k : Fin (bits p.val)) :
    CellSparse.lookup (bank N cell c aux g a x) (portBase N cell c edgeID portID aux v p + k.val) =
      external N cell c edgeID portID x p.val k :=
  (port_at N cell c edgeID portID aux g a x v p k).trans (external_port N cell c edgeID portID x v p k)

end Packing.CellAddresses

end BorderVNP
end Computability
end OAI

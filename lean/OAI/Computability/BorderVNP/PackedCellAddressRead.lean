import OAI.Computability.BorderVNP.PackedCellAddresses
import OAI.Computability.BorderVNP.CellGuessBlock

/-! # Absolute addresses on the actual assignment stack

The private stack begins with canonical internal wires, followed by the site
staging slabs. Supplied bits follow these guesses. Equality and profile rows
can reference any wire using a single base plus its lane number.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CellAddresses

open Crossing CellSparse
open private ends incidence from OAI.Computability.BorderVNP.PackedCellAddresses
open scoped Classical

variable {D m n s : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {C : Type} (cell : N.Site → C) (c : C) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable (aux : N.Site → ℕ)

/-- The supplied external block starts directly after all guessed words. -/
noncomputable def externalBase : ℕ := guessedSize N cell c + siteSize N cell c aux

/-- Absolute address of the first lane of a cable read by a fine site. -/
noncomputable def wireBase (v : {v : N.Site // cell v = c})
    (e : {e : N.Edge // N.src e = v.val ∨ N.dst e = v.val}) : ℕ :=
  if h : cell (N.src e.val) = cell (N.dst e.val) then
    CellSlabs.start (guessedRow N cell c edgeID) (fun u => N.width u.val)
      ⟨e.val, ends N cell c v.property e.property h⟩
  else externalBase N cell c aux + CellSlabs.start (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c)
    (.inl ⟨⟨e.val,h⟩, incidence N cell c v.property e.property⟩)

/-- Absolute start address of an attached argument port. -/
noncomputable def portBase (v : {v : N.Site // cell v = c}) (p : {p : P // N.attach p = v.val}) : ℕ :=
  externalBase N cell c aux + CellSlabs.start (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c)
    (.inr ⟨p.val, (congrArg cell p.property).trans v.property⟩)

/-- Physical bit order at the start of the local checker. -/
noncomputable def bank (g : Fin (guessedSize N cell c) → Bool) (a : Fin (siteSize N cell c aux) → Bool)
    (x : Fin (suppliedSize N cell c) → Bool) : List Bool :=
  List.ofFn g ++ (List.ofFn a ++ List.ofFn x)

private theorem read_external (g : Fin (guessedSize N cell c) → Bool)
    (a : Fin (siteSize N cell c aux) → Bool) (x : Fin (suppliedSize N cell c) → Bool)
    (i : Fin (suppliedSize N cell c)) :
    lookup (bank N cell c aux g a x) (externalBase N cell c aux + i.val) = x i := by
  simp only [bank,externalBase,Nat.add_assoc,lookup_after_prefix]
  simpa only [List.append_nil] using lookup_prefix x [] i

/-- Cable reads by the private machine use the shared guessed word or the appropriate crossing endpoint. -/
theorem wire_at (g : Fin (guessedSize N cell c) → Bool) (a : Fin (siteSize N cell c aux) → Bool)
    (x : Fin (suppliedSize N cell c) → Bool) (v : {v : N.Site // cell v = c})
    (e : {e : N.Edge // N.src e = v.val ∨ N.dst e = v.val}) (i : Fin (N.width e.val)) :
    lookup (bank N cell c aux g a x) (wireBase N cell c edgeID portID aux v e + i.val) =
      (wire N cell c edgeID portID v e i).elim g x := by
  by_cases h : cell (N.src e.val) = cell (N.dst e.val)
  · simp only [wireBase,wire,h,dite_true]
    exact lookup_prefix g (List.ofFn a ++ List.ofFn x) (CellSlabs.ordinal (guessedRow N cell c edgeID)
      (fun u => N.width u.val) ⟨⟨e.val,ends N cell c v.property e.property h⟩,i⟩)
  · simp only [wireBase,wire,h,dite_false,Sum.elim_inr,Nat.add_assoc]
    exact read_external N cell c aux g a x (suppliedOrdinal N cell c edgeID portID
      (.inl ⟨⟨e.val,h⟩,incidence N cell c v.property e.property⟩) i)

/-- An attached argument port reads the supplied value on every lane. -/
theorem port_at (g : Fin (guessedSize N cell c) → Bool) (a : Fin (siteSize N cell c aux) → Bool)
    (x : Fin (suppliedSize N cell c) → Bool) (v : {v : N.Site // cell v = c})
    (p : {p : P // N.attach p = v.val}) (i : Fin (bits p.val)) :
    lookup (bank N cell c aux g a x) (portBase N cell c edgeID portID aux v p + i.val) =
      x (port N cell c edgeID portID v p i) := by
  rw [portBase, Nat.add_assoc]
  exact read_external N cell c aux g a x (port N cell c edgeID portID v p i)

/-- Absolute address of a site staging bit in the macro's lookup language. -/
theorem site_at (siteID : N.Site ↪ Fin s) (g : Fin (guessedSize N cell c) → Bool)
    (a : Fin (siteSize N cell c aux) → Bool) (x : Fin (suppliedSize N cell c) → Bool)
    (v : {v : N.Site // cell v = c}) (i : Fin (aux v.val)) :
    lookup (bank N cell c aux g a x) (siteBase N cell c siteID aux v + i.val) =
      siteWords N cell c siteID aux a v i := by
  rw [bank,siteBase,Nat.add_assoc,lookup_after_prefix]
  exact lookup_prefix a (List.ofFn x) (CellSlabs.ordinal
    (((Function.Embedding.subtype _).trans siteID).trans Fin.valEmbedding) (fun v => aux v.val) ⟨v,i⟩)

end Packing.CellAddresses

end BorderVNP
end Computability
end OAI

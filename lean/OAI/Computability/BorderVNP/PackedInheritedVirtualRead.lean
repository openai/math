import OAI.Computability.BorderVNP.PackedInheritedVirtualBank

/-! # Reading intrinsic site bits through a virtual physical cell

Slicing any finite prefix of a bit bank into the virtual cell's three regions
provides a concrete physical cell assignment. At a site without internal
wires, its canonical cable and work reads therefore recover precisely the
intrinsic input and work vectors.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedProfile

open Crossing Inherited BankSite CellAddresses CellSparse
open scoped Classical

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (v : N.Site) (aux : N.Site → ℕ) {ns ne np : ℕ} (siteID : N.Site ↪ Fin ns)
variable (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)

/-- Slice a bit stream at the actual local region boundaries of every virtual cell. -/
noncomputable def cellView (bank : ℕ → Bool) : CellBanks N id aux where
  guessed _ i := bank i.val
  staged c i := bank (guessedSize N id c+i.val)
  supplied c i := bank (guessedSize N id c+siteSize N id c aux+i.val)

/-- Slicing the bit stream and reassembling its three blocks agrees on its full allocated extent. -/
theorem view_read (bank : ℕ → Bool) {k : ℕ} (hk : k < aux v + incoming N v) :
    (cellView N aux bank).read v k = bank k := by
  let g := guessedSize N id v
  let a := siteSize N id v aux
  let n := suppliedSize N id v
  let W := cellView N aux bank
  have ht : k < g+a+n := by
    have h := singleton_size N v aux
    change k < aux v + (g+n) at hk
    change a = aux v at h
    omega
  change lookup (List.ofFn (W.guessed v) ++ (List.ofFn (W.staged v) ++ List.ofFn (W.supplied v))) k = _
  by_cases hg : k < g
  · exact lookup_prefix _ _ (⟨k,hg⟩ : Fin g)
  have hga : k = g+(k-g) := by omega
  rw [hga,lookup_after_prefix]
  by_cases ha : k-g < a
  · exact lookup_prefix _ _ (⟨k-g,ha⟩ : Fin a)
  have hab : k-g = a+(k-g-a) := by omega
  rw [hab,lookup_after_prefix]
  have hread := lookup_prefix (W.supplied v) [] (⟨k-g-a,by omega⟩ : Fin n)
  simpa only [List.append_nil,cellView,W,Nat.add_assoc] using hread

/-- On a virtual singleton without an internal wire, its staged word reads the initial prefix. -/
theorem view_stage (empty : guessedSize N id v = 0) (bank : ℕ → Bool) (i : Fin (aux v)) :
    siteWords N id v siteID aux ((cellView N aux bank).staged v) ⟨v,rfl⟩ i = bank i.val := by
  let W := cellView N aux bank
  have h := site_at N id v aux siteID (W.guessed v) (W.staged v) (W.supplied v) ⟨v,rfl⟩ i
  rw [singleton_start N v aux siteID empty,zero_add] at h
  exact h.symm.trans (view_read N v aux bank (i.isLt.trans_le (Nat.le_add_right _ _)))

/-- The virtual cell reads the physical cable on its canonical lane, after the work prefix. -/
theorem view_cable (noLoop : ∀ z : Incident N v, N.src z.val ≠ N.dst z.val) (bank : ℕ → Bool)
    (z : Incident N v) (k : Fin (N.width z.val)) :
    (cellView N aux bank).wires edgeID portID v z.val k =
      bank (aux v+(sourceOrder N edgeID portID v (.inl ⟨z,k⟩)).val) := by
  let W := cellView N aux bank
  let idx := sourceOrder N edgeID portID v (.inl ⟨z,k⟩)
  have h := assignment_at N id v edgeID portID aux (W.guessed v) (W.staged v) (W.supplied v) ⟨v,rfl⟩ z k
  rw [singleton_wire N v aux edgeID portID noLoop z,Nat.add_assoc,← wireOrdinal] at h
  exact h.symm.trans (view_read N v aux bank (Nat.add_lt_add_left idx.isLt _))

/-- A complete input to the physical site table reads only its own incident cable values. -/
theorem view_wires_eq (noLoop : ∀ z : Incident N v, N.src z.val ≠ N.dst z.val)
    (b c : ℕ → Bool) (h : ∀ i : Fin (incoming N v), b (aux v+i.val) = c (aux v+i.val)) :
    (cellView N aux b).wires edgeID portID v = (cellView N aux c).wires edgeID portID v := by
  funext z k
  by_cases hv : N.src z = v ∨ N.dst z = v
  · exact (view_cable N v aux edgeID portID noLoop b ⟨z,hv⟩ k).trans
      ((h _).trans (view_cable N v aux edgeID portID noLoop c ⟨z,hv⟩ k).symm)
  · have hn : ¬(N.src z = v ∧ N.dst z = v) := fun h => hv (.inl h.1)
    simp [CellBanks.wires,assignment,hv,hn]

end Packing.InheritedProfile

end BorderVNP
end Computability
end OAI

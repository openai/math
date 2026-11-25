import OAI.Computability.BorderVNP.PackedInheritedPlacementTies
import OAI.Computability.BorderVNP.CellPacketFields

/-! # Numeric fields of the installed final incidence ties

Both half-open intervals of a tie fit the physical assignment bank. The
proof uses the ends of the allocated words, including a zero-width word at
the very end of its region. The finite row IDs determine ordering only.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Placement

open Crossing CellAddresses CellSparse
open scoped Classical

variable {D M np ns : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    {C : Type} (cell : N.Site → C) (c : C) (siteID : N.Site ↪ Fin ns)
    (edgeID : N.Edge ↪ Fin M) (portID : P ↪ Fin np) (state : N.Site → Site)
    (v : {v : N.Site // cell v = c})

/-- The physical cable or port word ends within the owning cell's three allocated regions. -/
theorem physicalStart_end_le (r : Row N v.val) :
    physicalStart N cell c edgeID portID state v r + width N v.val r ≤
      guessedSize N cell c + siteSize N cell c (fun u => (state u).size) + suppliedSize N cell c := by
  let aux := fun u => (state u).size
  cases r with
  | inl e =>
    change wireBase N cell c edgeID portID aux v e + N.width e.val ≤
      externalBase N cell c aux + suppliedSize N cell c
    unfold wireBase
    split
    · apply (CellSlabs.end_le_capacity _ _ _).trans
      change guessedSize N cell c ≤ guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c
      omega
    · rw [Nat.add_assoc]
      exact Nat.add_le_add_left (CellSlabs.end_le_capacity _ _ _) _
  | inr p =>
    change portBase N cell c edgeID portID aux v p + bits p.val ≤
      externalBase N cell c aux + suppliedSize N cell c
    rw [portBase,Nat.add_assoc]
    exact Nat.add_le_add_left (CellSlabs.end_le_capacity _ _ _) _

/-- The staged copy of the row ends within the site's actual allocated slab. -/
theorem stagedStart_end_le (hin : (state v.val).incoming = incoming N v.val) (r : Row N v.val) :
    siteBase N cell c siteID (fun u => (state u).size) v + (state v.val).work +
      localStart N edgeID portID v.val r + width N v.val r ≤
      guessedSize N cell c + siteSize N cell c (fun u => (state u).size) := by
  have localEnd : localStart N edgeID portID v.val r + width N v.val r ≤ incoming N v.val := by
    cases r with
    | inl e => exact wireEnd_le N edgeID portID v.val e
    | inr p => exact portEnd_le N edgeID portID v.val p
  have h := siteBase_fits N cell c siteID (fun u => (state u).size) v
  change siteBase N cell c siteID (fun u => (state u).size) v + ((state v.val).work+(state v.val).incoming) ≤ _ at h
  rw [hin] at h
  omega

/-- All numeric guard fields of one installed equality are bounded by the bank
length plus one. The extra one also covers the unit lane stride when the bank is empty. -/
theorem tie_guardBound (hin : (state v.val).incoming = incoming N v.val) (r : Row N v.val) :
    (tie N cell c siteID edgeID portID state v r).GuardBound
      (guessedSize N cell c + siteSize N cell c (fun u => (state u).size) + suppliedSize N cell c + 1) := by
  have hl := stagedStart_end_le N cell c siteID edgeID portID state v hin r
  have hr := physicalStart_end_le N cell c edgeID portID state v r
  let U := guessedSize N cell c + siteSize N cell c (fun u => (state u).size) + suppliedSize N cell c + 1
  change 1 ≤ U ∧ width N v.val r ≤ U ∧
    (siteBase N cell c siteID (fun u => (state u).size) v+(state v.val).work+localStart N edgeID portID v.val r ≤ U ∧
      0 ≤ U ∧ 1 ≤ U) ∧ (physicalStart N cell c edgeID portID state v r ≤ U ∧ 0 ≤ U ∧ 1 ≤ U)
  dsimp only [U]
  omega

/-- Every installed final tie satisfies the compact guard bound, in its actual public row order. -/
theorem ties_guardBound (hin : (state v.val).incoming = incoming N v.val) (r : Record)
    (hr : r ∈ ties N cell c siteID edgeID portID state v) :
    r.GuardBound (guessedSize N cell c + siteSize N cell c (fun u => (state u).size) + suppliedSize N cell c + 1) := by
  obtain ⟨row,_,rfl⟩ := List.mem_map.mp hr
  exact tie_guardBound N cell c siteID edgeID portID state v hin row

/-- The full transported fields of every final binding record satisfy the same local bound. -/
theorem ties_recordFields (hin : (state v.val).incoming = incoming N v.val) (r : Record)
    (hr : r ∈ ties N cell c siteID edgeID portID state v) :
    Packet.RecordFields r (guessedSize N cell c + siteSize N cell c (fun u => (state u).size) +
      suppliedSize N cell c + 1) := by
  obtain ⟨row,_,rfl⟩ := List.mem_map.mp hr
  exact ⟨tie_guardBound N cell c siteID edgeID portID state v hin row,trivial⟩

/-- The transported equality has nine scalar fields regardless of its width and base addresses. -/
theorem ties_record_length (r : Record) (hr : r ∈ ties N cell c siteID edgeID portID state v) :
    (Packet.record r).length = 9 := by
  obtain ⟨row,_,rfl⟩ := List.mem_map.mp hr
  rfl

end Packing.Inherited.Placement

end BorderVNP
end Computability
end OAI

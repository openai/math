import OAI.Computability.BorderVNP.PackedBankSortedCell
import OAI.Computability.BorderVNP.PackedBankRoundRowSize

/-! # Fixed public row sizes in the final owner-sorted directory

The directory merges the live site programs in their physical order, then
ties the staged site input to the final incident wires. The following bounds
apply to the actual directory consumed by the private cell compiler.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalCell

open Crossing CellSparse InheritedBank CellAddresses

variable {D s n p : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (owner : Fin s → ℕ)
  (N : Network D P bits) (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin n)
  (portID : P ↪ Fin p) (state : N.Site → Site) (c : ℕ) (reports : List (List ℕ))

local notation "dir" => directory owner N cell siteID edgeID portID state c reports

/-- The final translated rows have the same bound as the local rows. Each
extra incidence binding is a single equality occupying nine scalars. -/
theorem directory_rowBound {R : ℕ} (hR : 9 ≤ R) (h : ∀ v ∈ sites siteID owner c, (state v).RowBound R) :
    ∀ r ∈ (dir).records, (Packet.record r).length ≤ R := by
  intro r hr
  obtain ⟨v,hv,hmem⟩ := List.mem_flatMap.mp hr
  rcases List.mem_append.mp hmem with hp | ht
  · exact (state v).rowBound_placed (h v hv) _ _ r hp
  · obtain ⟨k,_,rfl⟩ := List.mem_map.mp ht
    exact hR

/-- All actual final profiles have selector widths admitted by the native
packet-to-statement compiler. Box relocation and final ties preserve this
property. -/
theorem directory_profileWidths (h : ∀ v ∈ sites siteID owner c, (state v).Schema) :
    (dir).ProfileWidths := by
  intro r hr
  obtain ⟨v,hv,hmem⟩ := List.mem_flatMap.mp hr
  rcases List.mem_append.mp hmem with hp | ht
  · obtain ⟨t,hm,rfl⟩ := List.mem_map.mp hp
    have hw := (h v hv t hm).2
    cases t <;> exact hw
  · obtain ⟨k,_,rfl⟩ := List.mem_map.mp ht
    exact trivial

end Packing.Inherited.FinalCell

end BorderVNP
end Computability
end OAI

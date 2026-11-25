import OAI.Computability.BorderVNP.PackedBankPacketProfiles
import OAI.Computability.BorderVNP.CellTypedRecordSize

/-! # Public scalar field count per site template

The alphabet size is fixed by the paid crossing identity before the input length
is selected. The number of scalars in a single origin or terminal row therefore
has a uniform bound independent of the values loaded from the physical header.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- Relocation preserves the number of source scalars in every wiring record. -/
@[simp] theorem Record.packet_length_shift (r : Record) (off : ℕ) :
    (Packet.record (r.shift off)).length = (Packet.record r).length := by
  cases r with
  | profile c p w hs rs => simp only [shift,Packet.record_profile_length,List.length_map]
  | zero | equal | box => rfl

end CellSparse

namespace Packing.BankCircuit

open CellSparse Crossing.Profile.Cell

/-- One source profile plus one scalar-field-bounded equality or zero pin per spoke. -/
theorem originList_row_size {D A : ℕ} (b : ℕ) (w : Header D A → ℕ) (first : Fin D × Bool) :
    ∀ r ∈ originList b w first, (Packet.record r).length ≤ 16*(A+1) := by
  simp only [originList,originRecords,List.forall_mem_append,List.forall_mem_cons,allRows,List.forall_mem_ofFn_iff,
    Packet.record_profile_length,List.length_ofFn,List.length_nil,Nat.mul_zero,Nat.add_zero]
  refine ⟨⟨by omega,fun _ => ?_⟩,fun _ => ?_⟩
  · change 9 ≤ _; omega
  · change 6 ≤ _; omega

/-- A terminal carries one route and one advertised multiplicity per fixed alphabet symbol. -/
theorem terminalList_row_size {D A : ℕ} (b : ℕ) (w : Header D A → ℕ) :
    ∀ r ∈ terminalList b w, (Packet.record r).length ≤ 16*(A+1) := by
  simp only [terminalList,terminalRecord,Crossing.Profile.Cell.routes,List.forall_mem_cons,allRows,
    List.forall_mem_ofFn_iff,Packet.record_profile_length,List.length_ofFn]
  exact ⟨by omega,fun _ => show 6 ≤ 16*(A+1) by omega⟩

end Packing.BankCircuit

namespace Packing.BankPacket

open CellSparse BankCircuit

/-- The bound holds for each actual emitted and relocated physical origin row. -/
theorem origin_read_row_size {D A : ℕ} (b : ℕ) (x : SiteInput D A → ℕ) (first : Fin D × Bool) :
    ∀ r ∈ (origin (A := A) b first).map (RecordCode.read x), (Packet.record r).length ≤ 16*(A+1) := by
  rw [origin_read,List.forall_mem_append,List.forall_mem_map]
  simp only [Record.packet_length_shift,allRows,List.forall_mem_ofFn_iff]
  exact ⟨originList_row_size _ _ _,fun _ => show 9 ≤ 16*(A+1) by omega⟩

/-- Each actual terminal row satisfies the same bound after its address shifts and ties. -/
theorem terminal_read_row_size {D A : ℕ} (b : ℕ) (x : SiteInput D A → ℕ) :
    ∀ r ∈ (terminal (D := D) (A := A) b).map (RecordCode.read x), (Packet.record r).length ≤ 16*(A+1) := by
  rw [terminal_read,List.forall_mem_append,List.forall_mem_map]
  simp only [Record.packet_length_shift,List.forall_mem_cons,List.forall_mem_ofFn_iff]
  exact ⟨terminalList_row_size _ _, show 9 ≤ 16*(A+1) by omega, fun _ => show 9 ≤ 16*(A+1) by omega⟩

end Packing.BankPacket

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.PackedBankPacketProfiles
import OAI.Computability.BorderVNP.CellProfileWidths

/-! # Width admissibility of the physical crossing profile templates

Origin and terminal sites encode an alphabet of size `A` using its ceiling
binary logarithm and supply exactly one histogram field for each alphabet
element. Relocating these ports and adding wiring ties preserves that fact.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- Moving physical wire ports leaves the selector width and histogram lengths unchanged. -/
@[simp] theorem Record.profileWidthOK_shift (r : Record) (off : ℕ) :
    (r.shift off).ProfileWidthOK ↔ r.ProfileWidthOK := by cases r <;> rfl

end CellSparse

namespace Crossing.Profile.Cell

open CellSparse

variable {A : ℕ}

/-- A terminal uses the actual histogram alphabet as its selector bound. -/
theorem terminalRecord_widthOK (j b : ℕ) (p : Fin A → ℕ) (s orig : Port) (compact : Fin A → Port) :
    (terminalRecord j b p s orig compact).ProfileWidthOK := by
  simp only [terminalRecord,Record.ProfileWidthOK,List.length_ofFn]
  exact Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

/-- The reference profile and all selector equality records at an origin have admissible widths. -/
theorem originRecords_widthOK {P : Type} [Fintype P] (j : ℕ) (p : Fin A → ℕ) (first : P) (spokes : P → Port) :
    ∀ r ∈ originRecords j p first spokes, r.ProfileWidthOK := by
  simp only [originRecords,List.forall_mem_cons,List.forall_mem_ofFn_iff,Record.ProfileWidthOK,List.length_ofFn]
  exact ⟨Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le,fun _ => trivial⟩

end Crossing.Profile.Cell

namespace Packing.BankCircuit

open CellSparse Crossing.Profile.Cell

/-- Padding rows in an origin's physical header do not introduce a new profile. -/
theorem originList_widthOK {D A : ℕ} (b : ℕ) (w : Header D A → ℕ) (first : Fin D × Bool) :
    ∀ r ∈ originList b w first, r.ProfileWidthOK := by
  rw [originList,List.forall_mem_append]
  refine ⟨originRecords_widthOK _ _ _ _,?_⟩
  simp [allRows,readPadding,Record.ProfileWidthOK]

/-- The physical terminal header adds zero pins to its admissible profile record. -/
theorem terminalList_widthOK {D A : ℕ} (b : ℕ) (w : Header D A → ℕ) :
    ∀ r ∈ terminalList b w, r.ProfileWidthOK := by
  rw [terminalList,List.forall_mem_cons]
  refine ⟨terminalRecord_widthOK ..,?_⟩
  simp [allRows,readPadding,Record.ProfileWidthOK]

end Packing.BankCircuit

namespace Packing.BankPacket

open CellSparse BankCircuit

/-- The origin packet decoded from the native site operand fields meets the compiler width condition. -/
theorem origin_read_widthOK {D A : ℕ} (b : ℕ) (x : SiteInput D A → ℕ) (first : Fin D × Bool) :
    ∀ r ∈ (origin (A := A) b first).map (RecordCode.read x), r.ProfileWidthOK := by
  rw [origin_read,List.forall_mem_append,List.forall_mem_map]
  refine ⟨fun r hr => (r.profileWidthOK_shift _).mpr (originList_widthOK b _ first r hr),?_⟩
  simp [allRows,bind,Record.ProfileWidthOK]

/-- A decoded terminal packet meets the same condition after all address shifts and feeder ties. -/
theorem terminal_read_widthOK {D A : ℕ} (b : ℕ) (x : SiteInput D A → ℕ) :
    ∀ r ∈ (terminal (D := D) (A := A) b).map (RecordCode.read x), r.ProfileWidthOK := by
  rw [terminal_read,List.forall_mem_append,List.forall_mem_map]
  refine ⟨fun r hr => (r.profileWidthOK_shift _).mpr (terminalList_widthOK b _ r hr),?_⟩
  simp [bind,Record.ProfileWidthOK]

end Packing.BankPacket

end BorderVNP
end Computability
end OAI

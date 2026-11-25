import OAI.Computability.BorderVNP.PackedInheritedWorkPublicCap

/-! # Merged physical address room from the expanded public-program budget -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening Epoch Epoch.Round CellAddresses
open scoped Classical

variable {D : ℕ} {P C : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (programs : Site.Programs N) (cell : N.Site → C) (c : C)

/-- The complete cell address range is bounded by the actual public descriptors and
private expanded work at that cell, including every canonical and staged wire. -/
theorem merged_program_capacity :
    guessedSize N cell c + siteSize N cell c (fun v => (programs v).program.size) + suppliedSize N cell c ≤
      3*localRecords N true programs.bankFields.prior programs.bankFields.payload (fun v => cell v=c) := by
  apply stagedCapacity_le N cell c _ _ _ 2
  intro v
  let data := programs.bankFields
  let one := localRecords N true data.prior data.payload (fun u => u=v)
  have hw : (programs v).program.work ≤ one := by
    apply (Nat.le_add_right _ _ : (programs v).program.work ≤ (programs v).program.expandedLoad).trans
    change data.payload v ≤ one
    simp [one,localRecords,testedWidth,boxCost,recordCost]
    omega
  have hi : (programs v).program.incoming ≤ one := (programs v).size.le.trans
    (wireCapacity_le N id v data.prior data.payload)
  exact (Nat.add_le_add hw hi).trans_eq (two_mul _).symm

/-- Word-fit corollary for the address frame on the selected final cell. -/
theorem merged_program_room {bound w : ℕ}
    (cap : localRecords N true programs.bankFields.prior programs.bankFields.payload (fun v => cell v=c) ≤ bound)
    (fit : 3*bound < 2^w) :
    guessedSize N cell c + siteSize N cell c (fun v => (programs v).program.size) + suppliedSize N cell c < 2^w :=
  (merged_program_capacity N programs cell c).trans_lt ((Nat.mul_le_mul_left 3 cap).trans_lt fit)

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI

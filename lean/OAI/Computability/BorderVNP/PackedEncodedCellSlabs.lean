import OAI.Computability.BorderVNP.PackedFinalTieNatural
import OAI.Computability.BorderVNP.PackedCellAddressRead

/-! # Bit readout under the native encoding of a finite cell number

The private and supplied arrays are the same ordered lists at the native
cell numeral and at the true finite owner. In particular the site slab read
at its public sparse row contains the same bits in both descriptions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalTies

open Crossing CellAddresses CellSparse
open scoped Classical
open private site from OAI.Computability.BorderVNP.PackedFinalTieNatural

variable {D ns C : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
variable (N : Network D P bits) (cell : N.Site → Fin C) (c : Fin C) (state : N.Site → Site)
variable (siteID : N.Site ↪ Fin ns)
local notation3 "key" => fun v => (cell v).val
local notation3 "size" => fun v => (state v).size
local notation3 "widths" => FinalReports.bank_sizes N cell state c

/-- The native list of private-wire bits, site staging and supplied bits is exactly
the finite owner's bank, in its original bit order. -/
theorem bank_nat (g : Fin (guessedSize N cell c) → Bool) (a : Fin (siteSize N cell c size) → Bool)
    (x : Fin (suppliedSize N cell c) → Bool) :
    bank N key c.val size (g ∘ Fin.cast widths.1) (a ∘ Fin.cast widths.2.1) (x ∘ Fin.cast widths.2.2) =
      bank N cell c size g a x := by
  have castWords {u v : ℕ} (h : u=v) (f : Fin v → Bool) : List.ofFn (f ∘ Fin.cast h)=List.ofFn f := by
    subst v
    rfl
  simp only [bank,castWords]

/-- The actual RAM read at a finite owner's sparse site rank agrees with the
read at its natural-number label, for the complete staged site word. -/
theorem siteWords_nat (a : Fin (siteSize N cell c size) → Bool) (v : {v : N.Site // cell v=c}) :
    siteWords N key c.val siteID size (a ∘ Fin.cast widths.2.1) ⟨v.val,congrArg Fin.val v.property⟩ =
      siteWords N cell c siteID size a v := by
  let g : Fin (guessedSize N cell c) → Bool := fun _ => false
  let x : Fin (suppliedSize N cell c) → Bool := fun _ => false
  let vv : {v : N.Site // key v=c.val} := ⟨v.val,congrArg Fin.val v.property⟩
  funext j
  have num := site_at N key c.val size siteID (g ∘ Fin.cast widths.1) (a ∘ Fin.cast widths.2.1)
    (x ∘ Fin.cast widths.2.2) vv j
  rw [bank_nat N cell c state g a x,site N cell c siteID state v] at num
  exact num.symm.trans (site_at N cell c size siteID g a x v j)

end Packing.Inherited.FinalTies

end BorderVNP
end Computability
end OAI

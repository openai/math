import OAI.Computability.BorderVNP.PackedEncodedCellSlabs

/-! # The true finite owner's incoming wire and port bits at the native cell numeral -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalTies

open Crossing CellAddresses CellSparse
open scoped Classical
open private wire port from OAI.Computability.BorderVNP.PackedFinalTieNatural

variable {D m np C : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
variable (N : Network D P bits) (cell : N.Site → Fin C) (c : Fin C) (state : N.Site → Site)
variable (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin np)
local notation3 "key" => fun v => (cell v).val
local notation3 "size" => fun v => (state v).size
local notation3 "widths" => FinalReports.bank_sizes N cell state c

/-- Encoding the cell by its physical numeral preserves every incident cable
and argument port of its canonical incoming vector, including loops. -/
theorem canonical_nat (v : {v : N.Site // cell v=c}) (g : Fin (guessedSize N cell c) → Bool)
    (x : Fin (suppliedSize N cell c) → Bool) :
    Placement.canonical N key c.val edgeID portID ⟨v.val,congrArg Fin.val v.property⟩
      (g ∘ Fin.cast widths.1) (x ∘ Fin.cast widths.2.2) =
      Placement.canonical N cell c edgeID portID v g x := by
  let a : Fin (siteSize N cell c size) → Bool := fun _ => false
  let vv : {v : N.Site // key v=c.val} := ⟨v.val,congrArg Fin.val v.property⟩
  apply congrArg₂ (inputWords N edgeID portID v.val)
  · funext e j
    have num := wire_at N key c.val edgeID portID size (g ∘ Fin.cast widths.1) (a ∘ Fin.cast widths.2.1)
      (x ∘ Fin.cast widths.2.2) vv e j
    rw [bank_nat N cell c state g a x,wire N cell c edgeID portID state v e] at num
    exact num.symm.trans (wire_at N cell c edgeID portID size g a x v e j)
  · funext p j
    have num := port_at N key c.val edgeID portID size (g ∘ Fin.cast widths.1) (a ∘ Fin.cast widths.2.1)
      (x ∘ Fin.cast widths.2.2) vv p j
    rw [bank_nat N cell c state g a x,port N cell c edgeID portID state v p] at num
    exact num.symm.trans (port_at N cell c edgeID portID size g a x v p j)

end Packing.Inherited.FinalTies

end BorderVNP
end Computability
end OAI

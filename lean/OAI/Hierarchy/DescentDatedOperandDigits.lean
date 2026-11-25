import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Numeric codes for the physically gathered ordinary operand fields -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Operand
open DescentSIMDLookup
noncomputable section
variable {cap : ℕ}

/-- The zero pointer is unused. The other numbers select a previous outgoing
slot and one of the eleven physical raw-edge roles at the fixed block. -/
def ticket (slot : Fin cap) (role : Fin 11) := 1+11*slot.val+role.val

def decode (cap idx : ℕ) : Option (Fin cap×Fin 11) :=
  if idx=0 then none else
  if live : (idx-1)/11<cap then some (⟨(idx-1)/11,live⟩,⟨(idx-1)%11,Nat.mod_lt _ (by decide)⟩) else none

theorem decode_ticket (slot : Fin cap) (role : Fin 11) : decode cap (ticket slot role)=some (slot,role) := by
  have bound:=role.isLt
  have hi : (ticket slot role-1)/11=slot.val := by unfold ticket;omega
  have lo : (ticket slot role-1)%11=role.val := by unfold ticket;omega
  have zero : ticket slot role≠0 := by unfold ticket;omega
  simp only [decode,ite_eq_right zero,dite_eq_left (hi.trans_lt slot.isLt)]
  exact congrArg some (Prod.ext (Fin.ext hi) (Fin.ext lo))

def flagCell (size : ℕ) (bit : Bool) : Cell (size+2) :=
  ⟨bit.toNat,by
    have room : 2^1≤2^(size+2) := Nat.pow_le_pow_right (by decide) (by omega)
    have bound : bit.toNat≤1:=by cases bit <;> decide
    norm_num at room
    omega⟩

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Operand

end OAI
